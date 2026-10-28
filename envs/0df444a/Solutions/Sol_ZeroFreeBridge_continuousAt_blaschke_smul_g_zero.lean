-- Prove2me | solution 1 for ZeroFreeBridge.continuousAt_blaschke_smul_g_zero
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:44.41695+00:00
-- url     : https://prove2.me/submissions/bcdc661d-a30c-4ef4-b768-3f4d00a4907c

import Mathlib

/- PHASE 4 (dVP frontier, the last leaf — `B·g` continuous at the centre): discharges the sole
   mechanical hypothesis of `hfac0` (`DlvpZetaCentreFac.zeta_center_factorization`).

   `B = ∏ᶠ (canonicalFactor R u)^(-m u)` is a FINITE product (finite divisor support); every factor
   `(canonicalFactor R u ·)^(-m u)` is continuous at `0` because `canonicalFactor R u` is a quotient with
   nonvanishing denominator at `0` (the zero `u ≠ 0`, so `0 - u ≠ 0`) and its value `-R/u ≠ 0` there
   (so the `zpow` is continuous, `ContinuousAt.zpow₀`).  A finite product of continuous-at-`0` factors is
   continuous at `0` (`tendsto_finsetProd`); times the analytic `g` gives `ContinuousAt (B·g) 0`.

   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {R : ℝ} (hR : 0 < R) (m : ℂ → ℤ) {g : ℂ → ℂ}
    (hfin : (Function.support (fun u => -(m u))).Finite)
    (hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0) (hg_cont0 : ContinuousAt g 0) :
    ContinuousAt ((∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) • g) 0 := by
  -- finprod collapses to a Finset product
  have hFP : (∏ᶠ u, (canonicalFactor R u) ^ (-(m u)))
      = fun w => ∏ u ∈ hfin.toFinset, (canonicalFactor R u w) ^ (-(m u)) := by
    have hsub : Function.mulSupport (fun u => (canonicalFactor R u) ^ (-(m u))) ⊆ hfin.toFinset := by
      intro u hu
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro hnu
      apply hu
      funext w
      simp [hnu]
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    funext w
    exact Finset.prod_apply w hfin.toFinset _
  -- each factor is continuous at 0
  have hfactor : ∀ u ∈ hfin.toFinset,
      ContinuousAt (fun w => (canonicalFactor R u w) ^ (-(m u))) 0 := by
    intro u hu
    have hu0 := hsupp u hu
    have hden0 : (R : ℂ) * (0 - u) ≠ 0 := by
      simp only [zero_sub, mul_neg, neg_ne_zero]
      exact mul_ne_zero (by exact_mod_cast hR.ne') hu0
    have hbase : ContinuousAt (canonicalFactor R u) 0 := by
      rw [canonicalFactor_def]
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hden0
    have hbne : canonicalFactor R u 0 ≠ 0 := by
      rw [canonicalFactor_apply]
      apply div_ne_zero _ hden0
      simp only [mul_zero, sub_zero]
      exact pow_ne_zero 2 (by exact_mod_cast hR.ne')
    exact hbase.zpow₀ (-(m u)) (Or.inl hbne)
  have hBcont : ContinuousAt (∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0 := by
    rw [hFP]
    exact tendsto_finsetProd hfin.toFinset (fun u hu => (hfactor u hu).tendsto)
  exact hBcont.smul hg_cont0
