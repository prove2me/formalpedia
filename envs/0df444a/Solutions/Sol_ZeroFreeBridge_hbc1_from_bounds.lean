-- Prove2me | solution 1 for ZeroFreeBridge.hbc1_from_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:04:56.252213+00:00
-- url     : https://prove2.me/submissions/a576aff0-c632-453e-948d-bc0da2d31ac7

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_bc_sum_blaschke
/- PHASE 4 (dVP frontier, item 3 — concrete-instantiation ring/geometry facts): the mechanical
   hypotheses of `dlvp_zeta_region_of_canonical_decomp` for the concrete centre `c₀ = 2 + iγ` and
   evaluation point `σ + iγ`.

   With the analytic inputs all in place (CanonicalDecomp, `norm_logDeriv_g_le_strip`,
   `zeta_zero_count_strip`, `hAL_arith`, `g_sphere_log_osc_strip`), the region theorem's remaining
   hypotheses at `c₀ = 2 + iγ` are pure ring/geometry/arithmetic:

     * `hcz`   `c₀ + ((σ+iγ) - c₀) = σ+iγ`                         (c₀ cancels; `ring`);
     * `hz`    `(σ+iγ) - c₀ ∈ ball 0 R`                            (`‖σ-2‖ = 2-σ < R`);
     * `hzne`  eval point is not a shifted zero                    (ζ(σ+iγ) ≠ 0, `Re = σ > 1`);
     * `hβσ`   `β < σ`                                             (`σ > 1 > β`).

   These discharge the geometric/algebraic side of the concrete instantiation.
   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

section Concrete
variable (σ γ R : ℝ)



/-- The recentred evaluation point is the REAL number `σ - 2`. -/
theorem concrete_eval_eq :
    (σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
  push_cast; ring

/-- `hz`: `(σ+iγ) - c₀ ∈ ball 0 R`, given `2 - σ < R` and `σ ≤ 2` (`‖σ-2‖ = 2-σ < R`). -/
theorem concrete_hz_mem (hσ2 : σ ≤ 2) (hσR : 2 - σ < R) :
    (σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) ∈ ball (0 : ℂ) R := by
  rw [mem_ball_zero_iff, concrete_eval_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
  linarith



/-- `hzne`: the recentred eval point `(σ+iγ) - c₀` is not a divisor-support point (a shifted zero),
    because `ζ(σ+iγ) ≠ 0` (`Re = σ > 1`) while every support point `u` gives a zero `ζ(c₀+u) = 0`. -/
theorem concrete_hzne {c₀ : ℂ} {R : ℝ} (σ γ : ℝ)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (heval_ne : riemannZeta (c₀ + ((σ : ℂ) + (γ : ℂ) * I - c₀)) ≠ 0)
    {u : ℂ} (hu : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0) :
    (σ : ℂ) + (γ : ℂ) * I - c₀ ≠ u := by
  have huball : u ∈ ball (0 : ℂ) R :=
    (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
      (Function.mem_support.mpr hu)
  have hord : analyticOrderAt (fun w => riemannZeta (c₀ + w)) u ≠ 0 := by
    intro h0; apply hu; rw [hf_ana.divisor_apply huball, h0]; rfl
  have hz0 := apply_eq_zero_of_analyticOrderAt_ne_zero
    (f := fun w => riemannZeta (c₀ + w)) (z₀ := u) hord
  intro h
  apply heval_ne
  rw [h]; exact hz0



end Concrete
end ZeroFreeBridge


/- PHASE 4 (dVP frontier, corrected assembly — the concrete BC-SUM building block): produce the
   height-γ `hbc₁` that the LOWER-layer region theorem `dlvp_zeta_region_of_bc_sums`
   (`DlvpZetaBcBridge`) consumes, for the ρ₀-enclosing disk `c₀ = 2+iγ`, eval point `σ+iγ`.

   The concrete-instantiation analysis (2026-09-06) found that the top layer
   `dlvp_zeta_region_of_canonical_decomp` is over-constrained (one c₀/disk for BOTH heights, but
   σ+2iγ is ≈|γ| away from c₀=2+iγ).  The correct target is `dlvp_zeta_region_of_bc_sums`, which
   needs the two BC-SUM INEQUALITIES hbc₁ (height γ) and hbc₂ (height 2γ) from appropriately-
   centred disks.  This wrapper produces hbc₁: it discharges the geometric hypotheses of
   `bc_sum_blaschke` (`hz` via `concrete_hz_mem`, `hzne` via `concrete_hzne`) and takes the
   structural/analytic inputs (D, g analyticity, `hg_bound` via `norm_logDeriv_g_le_strip`,
   `hAL` via `zeta_zero_count_strip`→`sum_abs_divisor_eq`→`hAL_arith`) as hypotheses.  Its output
   is EXACTLY the `hbc₁` shape (`.re` of the Herglotz sum, `s₁ = hfin.toFinset`).
   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn Metric
namespace ZeroFreeBridge

/-- Concrete height-γ BC-SUM on the disk `c₀ = 2+iγ` at eval `σ+iγ`: discharges hz/hzne via the
    concrete geometry lemmas and calls `bc_sum_blaschke`. Produces the `hbc₁` that
    `dlvp_zeta_region_of_bc_sums` consumes. -/
theorem bc_sum_concrete (σ γ : ℝ) {R : ℝ} (hR : 0 < R) (hσ2 : σ ≤ 2) (hσR : 2 - σ < R)
    (g : ℂ → ℂ)
    (D : CanonicalDecomp (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) g R)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R))
    (hg_ana : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball (0:ℂ) R, g w ≠ 0)
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u))).Finite)
    (heval_ne : riemannZeta (((2:ℂ) + (γ:ℂ)*I)
      + ((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I))) ≠ 0)
    {Bg AL : ℝ}
    (hg_bound : ‖logDeriv g ((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I))‖ ≤ Bg)
    (hAL : (∑ u ∈ hfin.toFinset,
        |(divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u : ℝ)|)
          / (R - ‖(σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I)‖) + Bg ≤ AL) :
    (-(logDeriv (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w))
        ((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I)))).re
      ≤ AL - (∑ u ∈ hfin.toFinset,
          (divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u : ℂ)
            / (((σ:ℂ) + (γ:ℂ)*I - ((2:ℂ) + (γ:ℂ)*I)) - u)).re := by
  refine bc_sum_blaschke hR D hf_ana hg_ana hg_ne hfin
    (concrete_hz_mem σ γ R hσ2 hσR) ?_ hg_bound hAL
  intro u hu
  have hune : divisor (fun w => riemannZeta (((2:ℂ) + (γ:ℂ)*I) + w)) (ball 0 R) u ≠ 0 := by
    have := hfin.mem_toFinset.mp hu
    simpa [Function.mem_support, neg_ne_zero] using this
  exact concrete_hzne σ γ hf_ana heval_ne hune

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 2 — the `hAL` arithmetic packaging): reduce the region theorem's
   `hAL` hypothesis `(∑ |divisor|)/(R-‖w‖) + Bg ≤ A·L` to the three O(L) component bounds plus a
   choice of `A`.

   `dlvp_zeta_region_of_canonical_decomp` (`DlvpZetaCanonical`) takes, at each height, the packed
   hypothesis `hAL : (∑_u |divisor u|)/(R - ‖w‖) + Bg ≤ A·L`.  Its three ingredients are each
   `O(L)`: the zero-count sum `S = ∑ |divisor u| ≤ Ccount·L` (Jensen), the entire-part bound
   `Bg ≤ CBg·L` (`norm_logDeriv_g_le_strip`), and the geometric gap `den = R - ‖w‖ > 0`.  Choosing
   `A ≥ Ccount/den + CBg` closes it.  This packaging is the mechanical last step of item 2 — it
   leaves only "supply the two O(L) constants and pick A" for the final concrete instantiation.

   conjecture1_proved = False (NOT a proof of RH).
-/


namespace ZeroFreeBridge



/-- The zero-count sum `∑ |divisor u|` equals `∑ divisor u` when the divisor is nonnegative (ζ has
    no poles), so the Jensen count `∑ divisor ≤ Ccount·L` feeds `hAL_arith` directly. -/
theorem sum_abs_divisor_eq {ι : Type*} (T : Finset ι) (D : ι → ℤ)
    (hD : ∀ u ∈ T, 0 ≤ D u) :
    ∑ u ∈ T, |(D u : ℝ)| = ∑ u ∈ T, (D u : ℝ) := by
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [abs_of_nonneg (by exact_mod_cast hD u hu)]

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item (A) — the height-γ hbc₁ wiring): produce the BC-SUM inequality
   `dlvp_zeta_region_of_bc_sums` consumes at height γ, from the O(L) bounds.

   With every analytic input now an explicit kernel-clean lemma (`hg_bound_gamma` for `Bg`,
   `sum_divisor_recenter_le_jensen` for the count `C`), closing `hbc₁` is composition: this wrapper
   takes `Bg`, `C`, and the region constraint `C/(R-‖z₀‖) + Bg ≤ AL`, derives `hAL` (via
   `sum_abs_divisor_eq` + `divisor ≥ 0` from `hf_ana.divisor_nonneg` + monotonicity in the count),
   and calls `bc_sum_concrete`.  Reusable for BOTH heights (the height-2γ `hbc₂` uses the same shape
   on the parallel disk).  `‖z₀‖ = 2-σ` via `concrete_eval_eq`.  conjecture1_proved = False.
-/



open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution (σ γ : ℝ) {R : ℝ} (hR : 0 < R) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hσR : 2 - σ < R)
    (g : ℂ → ℂ)
    (D : CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R))
    (hg_ana : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u))).Finite)
    (heval_ne : riemannZeta (((2 : ℂ) + (γ : ℂ) * I)
      + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))) ≠ 0)
    {Bg AL C : ℝ}
    (hg_bound : ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg)
    (hcount : (∑ u ∈ hfin.toFinset,
        (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ)) ≤ C)
    (hAL_bound : C / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg ≤ AL) :
    (-(logDeriv (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w))
        ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)))).re
      ≤ AL - (∑ u ∈ hfin.toFinset,
          (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℂ)
            / (((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) - u)).re := by
  refine bc_sum_concrete σ γ hR hσ2 hσR g D hf_ana hg_ana hg_ne hfin heval_ne hg_bound ?_
  -- ‖z₀‖ = 2 - σ
  have hznorm : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ = 2 - σ := by
    rw [concrete_eval_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    ring
  have hden : (0 : ℝ) < R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ := by
    rw [hznorm]; linarith
  have hdivnn : ∀ u ∈ hfin.toFinset,
      0 ≤ divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u :=
    fun u _ => hf_ana.divisor_nonneg u
  rw [sum_abs_divisor_eq hfin.toFinset _ hdivnn]
  have hmono : (∑ u ∈ hfin.toFinset,
      (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ))
        / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖)
      ≤ C / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) := by
    gcongr
  linarith [hAL_bound, hmono]
