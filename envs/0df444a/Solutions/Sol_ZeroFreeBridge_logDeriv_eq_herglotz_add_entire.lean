-- Prove2me | solution 1 for ZeroFreeBridge.logDeriv_eq_herglotz_add_entire
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:55.991411+00:00
-- url     : https://prove2.me/submissions/58c3c706-910e-4477-92b0-b66571f8ed9f

import Mathlib
import Theorems.Thm_ZeroFreeBridge_logDeriv_canonicalFactor
import Theorems.Thm_ZeroFreeBridge_logDeriv_split_off_zeros

/- PHASE 4 (dVP frontier, BLASCHKE item (d4) core): the ζ log-derivative in Herglotz + entire-part
   form, with the canonical (Blaschke) factors.

   Expanding `DlvpBlaschkeSplit.logDeriv_split_off_zeros` via `DlvpCanonicalLogDeriv.logDeriv_
   canonicalFactor` and `n u = -divisor u` gives the dVP explicit-formula shape:

     `logDeriv ζ z = Σ_ρ (divisor ρ)/(z-ρ)  +  [ Σ_ρ (divisor ρ)·conj ρ/(R²-conj ρ·z) + logDeriv g z ]`,

   i.e. `ζ'/ζ = Z + E` with `Z` the Herglotz zero-sum (Re ≥ 0 near the line, droppable) and the entire
   part `E` = correction + `logDeriv g` bounded `O(L)` by `DlvpCorrectionBound` + item (c).  This is
   exactly the `w = Z + E` input to the reduction skeleton `DlvpBCSum`.  conjecture1_proved = False.
-/



open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R)
    (hf_ana : AnalyticOnNhd ℂ f (ball 0 R)) (hg_ana : AnalyticOnNhd ℂ g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hzne : ∀ u ∈ hfin.toFinset, z ≠ u) :
    logDeriv f z
      = (∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u))
        + ((∑ u ∈ hfin.toFinset,
              (divisor f (ball 0 R) u : ℂ) * (starRingEnd ℂ) u
                / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z))
           + logDeriv g z) := by
  have hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) R := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hdu : divisor f (ball 0 R) u ≠ 0 := fun h => hu (by simp [h])
    exact (divisor f (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hdu)
  have hzR : ‖z‖ < R := by rw [← mem_ball_zero_iff]; exact hz
  have hA : (∑ u ∈ hfin.toFinset,
        ((-(divisor f (ball 0 R) u) : ℤ) : ℂ) * logDeriv (canonicalFactor R u) z)
      = (∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u))
        + (∑ u ∈ hfin.toFinset,
            (divisor f (ball 0 R) u : ℂ) * (starRingEnd ℂ) u
              / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have huR : ‖u‖ < R := by rw [← mem_ball_zero_iff]; exact hsupp u hu
    have hzu : z - u ≠ 0 := sub_ne_zero.mpr (hzne u hu)
    have hden : (R : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 := by
      intro h
      have h2 : ‖(starRingEnd ℂ) u * z‖ = R ^ 2 := by
        have : (starRingEnd ℂ) u * z = (R : ℂ) ^ 2 := by linear_combination -h
        rw [this]; simp [Complex.norm_real, abs_of_pos hR, sq]
      rw [norm_mul, RCLike.norm_conj] at h2
      nlinarith [h2, huR, hzR, norm_nonneg u, norm_nonneg z]
    rw [logDeriv_canonicalFactor hR.ne' hden hzu]
    push_cast
    ring
  rw [logDeriv_split_off_zeros D hf_ana hg_ana hg_ne hfin hz hzne, hA]
  ring
