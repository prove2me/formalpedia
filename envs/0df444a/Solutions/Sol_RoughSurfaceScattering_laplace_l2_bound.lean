-- Prove2me | solution 1 for RoughSurfaceScattering.laplace_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:14:55.981597+00:00
-- url     : https://prove2.me/submissions/f8883b5a-6069-4f60-bd9d-c1b83f48e26c

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric
open RoughSurfaceScattering

/-- `log² r ≤ (2R+2)²/r` for `0 < r < R`. -/
lemma log_sq_le_div (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    Real.log r ^ 2 ≤ (2 * R + 2) ^ 2 / r := by
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hsq : √r ^ 2 = r := Real.sq_sqrt hr.le
  have h1 : Real.log r = 2 * Real.log √r := by rw [Real.log_sqrt hr.le]; ring
  have h2 : Real.log √r ≤ √r := (Real.log_le_sub_one_of_pos hs).trans (by linarith)
  have h3 : -Real.log √r ≤ (√r)⁻¹ := by
    rw [← Real.log_inv]
    exact (Real.log_le_sub_one_of_pos (inv_pos.mpr hs)).trans (by linarith)
  have hinv : 0 < (√r)⁻¹ := inv_pos.mpr hs
  have h4 : Real.log √r ^ 2 ≤ (√r + (√r)⁻¹) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have h5 : r * (√r + (√r)⁻¹) ^ 2 = (r + 1) ^ 2 := by
    have hmul : √r * (√r)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
    have hinv2 : (√r)⁻¹ ^ 2 = r⁻¹ := by rw [inv_pow, hsq]
    have : r * (√r + (√r)⁻¹) ^ 2 =
        r * √r ^ 2 + 2 * r * (√r * (√r)⁻¹) + r * (√r)⁻¹ ^ 2 := by ring
    rw [this, hsq, hmul, hinv2, mul_inv_cancel₀ hr.ne']
    ring
  rw [le_div_iff₀ hr, h1]
  have : r * (2 * Real.log √r) ^ 2 ≤ 4 * (r + 1) ^ 2 := by
    rw [← h5]; nlinarith [h4]
  nlinarith [this]

/-- `Φ₀` depends only on `x - z`. -/
lemma phi0_sub (x z : R2) : Phi 0 x z = Phi 0 (x - z) 0 := by
  simp [Phi]

theorem solution (f : ℝ → ℝ) (s0 δ : ℝ) (D0 : Set R2) (hD0 : Bornology.IsBounded D0)
    (c : ℝ) :
    ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
      l2Norm D0 (fun x => (c : ℂ) * Phi 0 x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) ≤
        ENNReal.ofReal C := by
  obtain ⟨R, hR⟩ := hD0.subset_ball (gpt f s0)
  set R' : ℝ := max R 0 + |δ| * ‖normal f s0‖ + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  let h : R2 → ℂ := fun y => (c : ℂ) * Phi 0 y 0
  have hmeas : AEStronglyMeasurable h volume := by
    have : Measurable h := by
      simp only [h, Phi, if_true]
      fun_prop
    exact this.aestronglyMeasurable
  -- `|h y|² ≲ ‖y‖⁻¹` on the ball, hence `h ∈ L²(B_{R'})`
  have hmem : MemLp h 2 (volume.restrict (ball 0 R')) := by
    rw [memLp_two_iff_integrable_sq_norm hmeas.restrict]
    have hfin : Module.finrank ℝ R2 = 2 := finrank_euclideanSpace_fin
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (α := 1)
      (C := c ^ 2 * (1 / (2 * Real.pi)) ^ 2 * (2 * R' + 2) ^ 2)
      (by rw [hfin]; norm_num) (by rw [hfin]; norm_num) ?_ ?_
    · refine ae_restrict_of_forall_mem measurableSet_ball fun y hy => ?_
      have hyR : ‖y‖ < R' := by simpa using hy
      have hnorm : ‖h y‖ ^ 2 = c ^ 2 * (1 / (2 * Real.pi)) ^ 2 * Real.log ‖y‖ ^ 2 := by
        simp only [h, Phi, if_true, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          one_div, Real.log_inv, mul_pow, sq_abs, neg_sq]
        ring
      rw [Real.norm_of_nonneg (by positivity), hnorm, Real.rpow_neg_one]
      rcases eq_or_lt_of_le (norm_nonneg y) with h0 | hpos
      · rw [← h0]; simp
      · calc c ^ 2 * (1 / (2 * Real.pi)) ^ 2 * Real.log ‖y‖ ^ 2
            ≤ c ^ 2 * (1 / (2 * Real.pi)) ^ 2 * ((2 * R' + 2) ^ 2 / ‖y‖) :=
              mul_le_mul_of_nonneg_left (log_sq_le_div _ _ hpos hyR) (by positivity)
          _ = c ^ 2 * (1 / (2 * Real.pi)) ^ 2 * (2 * R' + 2) ^ 2 * ‖y‖⁻¹ := by ring
    · exact (continuous_norm.aestronglyMeasurable.pow 2).comp_aemeasurable hmeas.aemeasurable
        |>.congr (by rfl)
  refine ⟨(eLpNorm h 2 (volume.restrict (ball 0 R'))).toReal, fun j hj => ?_⟩
  rw [ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  set z := gpt f s0 - (δ / (j : ℝ)) • normal f s0 with hz
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hzx : dist (gpt f s0) z ≤ |δ| * ‖normal f s0‖ := by
    rw [hz, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_div,
      Nat.abs_cast]
    gcongr
    exact div_le_self (abs_nonneg _) hj1
  have hsub : D0 ⊆ ball z R' := by
    intro x hx
    have hx' := hR hx
    rw [mem_ball] at hx' ⊢
    calc dist x z ≤ dist x (gpt f s0) + dist (gpt f s0) z := dist_triangle _ _ _
      _ < R' := by have := le_max_left R 0; linarith
  have hfun : (fun x => (c : ℂ) * Phi 0 x z) = h ∘ (fun x => x - z) := by
    funext x
    simp only [Function.comp_apply, h, phi0_sub x z]
  have hpre : (fun x => x - z) ⁻¹' ball (0 : R2) R' = ball z R' := by
    ext x
    simp [dist_eq_norm]
  have hmp : MeasurePreserving (fun x => x - z) (volume.restrict (ball z R'))
      (volume.restrict (ball (0 : R2) R')) := by
    have := (measurePreserving_sub_right (volume : Measure R2) z).restrict_preimage
      (measurableSet_ball (x := (0 : R2)) (ε := R'))
    rwa [hpre] at this
  unfold l2Norm
  calc eLpNorm (fun x => (c : ℂ) * Phi 0 x z) 2 (volume.restrict D0)
      ≤ eLpNorm (fun x => (c : ℂ) * Phi 0 x z) 2 (volume.restrict (ball z R')) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
    _ = eLpNorm h 2 (volume.restrict (ball 0 R')) := by
        rw [hfun]
        exact eLpNorm_comp_measurePreserving hmeas.restrict hmp
