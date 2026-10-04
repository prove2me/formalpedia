-- Prove2me | solution 1 for PolyakovAction.conformal_gauge_constraints
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:48:07.08132+00:00
-- url     : https://prove2.me/submissions/2dce9bfe-b6ef-43c4-97d6-5e76954d5dfe

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

theorem PolyakovAction.minkowski2_inv_30ddb66b :
    (PolyakovAction.minkowskiMetric 2)⁻¹ = PolyakovAction.minkowskiMetric 2 := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PolyakovAction.minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_two]

theorem PolyakovAction.minkowski2_entries_30ddb66b :
    PolyakovAction.minkowskiMetric 2 0 0 = 1 ∧ PolyakovAction.minkowskiMetric 2 0 1 = 0 ∧
    PolyakovAction.minkowskiMetric 2 1 0 = 0 ∧ PolyakovAction.minkowskiMetric 2 1 1 = -1 := by
  simp [PolyakovAction.minkowskiMetric]

open PolyakovAction in
theorem solution {D : ℕ} (T : ℝ) (hT : T ≠ 0)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ) (X : Worldsheet → Spacetime D)
    (σ : Worldsheet) :
    stressEnergyTensor T g (fun _ => minkowskiMetric 2) X σ = 0 ↔
      (inducedMetric g X σ 0 1 = 0 ∧ inducedMetric g X σ 1 0 = 0 ∧
        inducedMetric g X σ 0 0 + inducedMetric g X σ 1 1 = 0) := by
  have hinv := PolyakovAction.minkowski2_inv_30ddb66b
  obtain ⟨m00, m01, m10, m11⟩ := PolyakovAction.minkowski2_entries_30ddb66b
  have key : ∀ a b : Fin 2, stressEnergyTensor T g (fun _ => minkowskiMetric 2) X σ a b
      = T * (inducedMetric g X σ a b - 1 / 2 * minkowskiMetric 2 a b *
          (inducedMetric g X σ 0 0 - inducedMetric g X σ 1 1)) := by
    intro a b
    simp only [stressEnergyTensor, Matrix.of_apply, hinv, Fin.sum_univ_two, m00, m01, m10, m11]
    ring
  generalize inducedMetric g X σ = M at key ⊢
  constructor
  · intro h
    have h00 := key 0 0
    have h01 := key 0 1
    have h10 := key 1 0
    rw [h, Matrix.zero_apply, m00] at h00
    rw [h, Matrix.zero_apply, m01] at h01
    rw [h, Matrix.zero_apply, m10] at h10
    have e00 : T * ((M 0 0 + M 1 1) / 2) = 0 := by linarith
    have e01 : T * M 0 1 = 0 := by linarith
    have e10 : T * M 1 0 = 0 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.mp e01).resolve_left hT
    · exact (mul_eq_zero.mp e10).resolve_left hT
    · have := (mul_eq_zero.mp e00).resolve_left hT
      linarith
  · rintro ⟨h01, h10, hs⟩
    have h11 : M 1 1 = -M 0 0 := by linarith
    ext a b
    rw [key, Matrix.zero_apply]
    revert a b
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [m00, h11]; ring
    · rw [m01, h01]; ring
    · rw [m10, h10]; ring
    · rw [m11, h11]; ring
