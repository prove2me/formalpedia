-- Prove2me | solution 1 for ZeroFreeBridge.norm_logDeriv_le_of_sphere_log_norm_le_interior
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:03:04.602767+00:00
-- url     : https://prove2.me/submissions/9c0d1d54-56e9-47b1-af41-922f60d23423

import Mathlib
import Theorems.Thm_ZeroFreeBridge_norm_logDeriv_le_of_log_norm_le_interior
/- PHASE 4 (dVP frontier, obligation (i-b') → SPHERE): reduce the entire-part bound to a bound on
   `log‖g‖` on the BOUNDARY sphere, via the maximum-modulus principle.

   `DlvpEntireBound.norm_logDeriv_le_of_log_norm_le` needs `log‖g z‖ - log‖g c‖ ≤ M'` throughout the
   OPEN disk.  But `log‖g‖ = Re(log g)` is harmonic, so its sup over the disk is attained on the
   boundary: `‖g‖ ≤ sup_{sphere}‖g‖` on the whole closed disk (`Complex.norm_le_of_forall_mem_frontier
   _norm_le`, max modulus for `g`).  Hence a bound on `log‖g‖` on the SPHERE propagates to the disk.

   This isolates the sole ζ-specific input as a SPHERE bound — exactly where `zeta_sphere_bound`
   (already proved) lives: `‖ζ z‖` bounded uniformly on spheres ⟹ `log‖ζ‖ = O(L)`.  Feeding
   `M' = A·L` gives `‖E‖ = O(L)`.  Function-agnostic max-modulus atom + ζ-ready composition.
   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

namespace ZeroFreeBridge

/-- **Maximum-modulus reduction.**  If `g` is holomorphic on `ball c R` and continuous up to the
    boundary (`DiffContOnCl`), then a uniform bound `‖g‖ ≤ B` on the sphere `sphere c R` propagates
    to the whole open disk. -/
theorem norm_le_on_ball_of_sphere {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : R ≠ 0)
    (hd : DiffContOnCl ℂ f (ball c R)) (hB : ∀ z ∈ sphere c R, ‖f z‖ ≤ B) :
    ∀ z ∈ ball c R, ‖f z‖ ≤ B := by
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_
    (subset_closure hz)
  rw [frontier_ball c hR]
  exact hB



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, entire-part PLUMBING): the two mechanical lemmas that connect the
   interior-point bound (`DlvpBCDerivInterior`) to the Blaschke BC-SUM (`bc_sum_blaschke`).

   (a) `norm_logDeriv_le_of_sphere_log_norm_le_interior` — the interior entire-part bound driven by a
       SPHERE oscillation bound (not the whole ball): `log‖g‖ = Re(log g)` is harmonic, so a boundary
       bound propagates to the disk by maximum modulus (`DlvpMaxMod.norm_le_on_ball_of_sphere`, via
       `exp`), and the resulting ball bound feeds `norm_logDeriv_le_of_log_norm_le_interior`.  This is
       exactly the shape available for ζ's Blaschke `g`, whose boundary `log‖g‖` equals `log‖ζ‖`
       (Blaschke factors have modulus 1 on the sphere).

   (b) `logDeriv_comp_const_add` — the RECENTRING: `bc_sum_blaschke` lives on `ball 0 R`, so ζ enters as
       `f(w) = ζ(c + w)`; its log-derivative is ζ's, shifted: `logDeriv (fun w => ζ(c+w)) z =
       logDeriv ζ (c+z)` (chain rule, `deriv (c+·) = 1`).

   conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {g : ℂ → ℂ} {c z₀ : ℂ} {R M' : ℝ}
    (hM' : 0 < M') (hρ : ‖z₀ - c‖ < R)
    (hd : DiffContOnCl ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hsphere : ∀ z ∈ sphere c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g z₀‖ ≤ 4 * M' * (R + ‖z₀ - c‖) / (R - ‖z₀ - c‖) ^ 2 := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hρ
  -- boundary bound on ‖g‖ from the log bound, then maximum modulus to the disk, then back to log
  set B : ℝ := Real.exp (M' + Real.log ‖g c‖) with hB_def
  have hgz_le : ∀ z ∈ sphere c R, ‖g z‖ ≤ B := by
    intro z hz
    rcases eq_or_lt_of_le (norm_nonneg (g z)) with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · calc ‖g z‖ = Real.exp (Real.log ‖g z‖) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (M' + Real.log ‖g c‖) := Real.exp_le_exp.mpr (by linarith [hsphere z hz])
        _ = B := rfl
  have hball_le : ∀ z ∈ ball c R, ‖g z‖ ≤ B := norm_le_on_ball_of_sphere hR.ne' hd hgz_le
  have hlog : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M' := by
    intro z hz
    have hgz_pos : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z hz)
    have hle : Real.log ‖g z‖ ≤ Real.log B := Real.log_le_log hgz_pos (hball_le z hz)
    rw [hB_def, Real.log_exp] at hle
    linarith
  exact norm_logDeriv_le_of_log_norm_le_interior hM' hρ hd.differentiableOn hne hlog
