-- Prove2me | solution 1 for ZeroFreeBridge.norm_blaschke_center_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:20.537387+00:00
-- url     : https://prove2.me/submissions/0f390bc4-fe18-4e2b-97a7-1697db5368ce

import Mathlib
/- PHASE 4 (dVP frontier, the Blaschke-CENTRE relation ‖B 0‖ ≤ 1 — item 2's last piece): the canonical
   Blaschke factor has modulus `R/‖w‖ > 1` at the centre, so raised to `-divisor` (`divisor ≥ 0` since the
   disk avoids the ζ pole) each factor has modulus `≤ 1`, and the finite product `‖B 0‖ ≤ 1`.

   Combined with the centre factorization `‖ζ c₀‖ = ‖f 0‖ = ‖B 0‖·‖g 0‖` this gives the Blaschke-centre
   relation `‖ζ c₀‖ ≤ ‖g 0‖` that `DlvpZetaEntire.norm_logDeriv_g_le` requires.  This file supplies the
   per-factor computational core.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex

namespace ZeroFreeBridge

/-- **Canonical factor at the centre.**  `‖canonicalFactor R w 0‖ = R/‖w‖`. -/
theorem norm_canonicalFactor_zero {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0) :
    ‖canonicalFactor R w 0‖ = R / ‖w‖ := by
  rw [canonicalFactor_apply, norm_div]
  have hnum : ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) w * 0‖ = R ^ 2 := by
    simp only [mul_zero, sub_zero, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hden : ‖(R : ℂ) * (0 - w)‖ = R * ‖w‖ := by
    simp only [zero_sub, mul_neg, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
  rw [hnum, hden, pow_two, mul_div_mul_left _ _ hR.ne']

/-- **Per-factor centre bound.**  For a zero `w` inside the disk (`0 < ‖w‖ < R`) with nonnegative
    multiplicity `n ≥ 0`, the canonical factor raised to `-n` has modulus `≤ 1` at the centre. -/
theorem norm_canonicalFactor_zpow_zero_le_one {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwR : ‖w‖ < R) {n : ℤ} (hn : 0 ≤ n) :
    ‖(canonicalFactor R w 0) ^ (-n)‖ ≤ 1 := by
  rw [norm_zpow, norm_canonicalFactor_zero hR hw0]
  -- (R/‖w‖)^(-n) ≤ 1, base > 1, exponent ≤ 0
  have hbase : (1 : ℝ) ≤ R / ‖w‖ := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < ‖w‖)]; linarith
  have : (R / ‖w‖) ^ (-n) ≤ (R / ‖w‖) ^ (0 : ℤ) := by
    apply zpow_le_zpow_right₀ hbase
    linarith
  simpa using this



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the Blaschke-CENTRE relation ‖B 0‖ ≤ 1 — item 2's last piece): the canonical
   Blaschke factor has modulus `R/‖w‖ > 1` at the centre, so raised to `-divisor` (`divisor ≥ 0` since the
   disk avoids the ζ pole) each factor has modulus `≤ 1`, and the finite product `‖B 0‖ ≤ 1`.

   Combined with the centre factorization `‖ζ c₀‖ = ‖f 0‖ = ‖B 0‖·‖g 0‖` this gives the Blaschke-centre
   relation `‖ζ c₀‖ ≤ ‖g 0‖` that `DlvpZetaEntire.norm_logDeriv_g_le` requires.  This file supplies the
   per-factor computational core.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge






theorem solution {R : ℝ} (hR : 0 < R) (m : ℂ → ℤ)
    (hfin : (Function.support (fun u => -(m u))).Finite)
    (hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0 ∧ ‖u‖ < R)
    (hm : ∀ u ∈ hfin.toFinset, 0 ≤ m u) :
    ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0‖ ≤ 1 := by
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
  rw [hFP, norm_prod]
  refine Finset.prod_le_one (fun u _ => norm_nonneg _) (fun u hu => ?_)
  obtain ⟨hu0, huR⟩ := hsupp u hu
  exact norm_canonicalFactor_zpow_zero_le_one hR hu0 huR (hm u hu)
