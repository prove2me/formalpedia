-- Prove2me | solution 1 for VectorSpaceOpt.bounded_iff_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:47:53.389291+00:00
-- url     : https://prove2.me/submissions/3219cdc1-5ec7-40bf-a103-46b37286f0f1

import Mathlib


theorem solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →ₗ[ℝ] ℝ) :
    (∃ M : ℝ, ∀ x : X, |f x| ≤ M * ‖x‖) ↔ Continuous f := by
  constructor
  · rintro ⟨M, hM⟩
    exact (f.mkContinuous M (fun x => by simpa [Real.norm_eq_abs] using hM x)).continuous
  · intro hc
    let F : X →L[ℝ] ℝ := ⟨f, hc⟩
    refine ⟨‖F‖, fun x => ?_⟩
    have := F.le_opNorm x
    rw [Real.norm_eq_abs] at this
    exact this
