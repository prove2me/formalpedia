-- Prove2me | solution 1 for PFluxContinuity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:10:43.703857+00:00
-- url     : https://prove2.me/submissions/3be3eee5-ae48-475f-ae06-5b99dd2e82b8

import Definitions.Def_PHigherOrder_PFlux
import Definitions.Def_PHigherOrder_PFluxContinuity

set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∀ ξ : Plane, ‖PFlux p ξ‖ = ‖ξ‖ ^ (p - 1)) ∧ Continuous (PFlux p) := by
  have h2 : p - 2 ≠ 0 := by intro hh; linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hnorm : ∀ ξ : Plane, ‖PFlux p ξ‖ = ‖ξ‖ ^ (p - 1) := by
    intro ξ
    rcases eq_or_ne ξ 0 with h | h
    · subst h; simp [PFlux, Real.zero_rpow h2, Real.zero_rpow hp1.ne']
    · have hn : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr h
      rw [PFlux, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hn.le _),
        ← Real.rpow_add_one hn.ne' (p - 2)]
      ring_nf
  refine ⟨hnorm, continuous_iff_continuousAt.mpr ?_⟩
  intro ξ₀
  rcases eq_or_ne ξ₀ 0 with h | h
  · subst h
    have hz : PFlux p (0 : Plane) = 0 := by simp [PFlux, Real.zero_rpow h2]
    have hz2 : ‖(0 : Plane)‖ ^ (p - 1) = 0 := by simp [Real.zero_rpow hp1.ne']
    have hcont : Filter.Tendsto (fun ξ : Plane => ‖ξ‖ ^ (p - 1)) (nhds 0) (nhds 0) := by
      have hc : ContinuousAt (fun ξ : Plane => ‖ξ‖ ^ (p - 1)) 0 :=
        ((Real.continuous_rpow_const hp1.le).comp continuous_norm).continuousAt
      have := hc.tendsto
      rwa [hz2] at this
    rw [ContinuousAt, hz, tendsto_zero_iff_norm_tendsto_zero]
    simpa [hnorm] using hcont
  · have hn : ‖ξ₀‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hs : ContinuousAt (fun ξ : Plane => ‖ξ‖ ^ (p - 2)) ξ₀ :=
      (Real.continuousAt_rpow_const _ _ (Or.inl hn)).comp continuous_norm.continuousAt
    exact hs.smul continuousAt_id
