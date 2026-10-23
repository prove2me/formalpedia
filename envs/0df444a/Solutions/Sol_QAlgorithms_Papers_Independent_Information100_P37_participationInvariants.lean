-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.participationInvariants
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:25:04.26327+00:00
-- url     : https://prove2.me/submissions/713e6d01-e8a9-468f-a6f4-4b93a0d69cae

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

open QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (response U).trace = (Fintype.card ι : ℝ) - totalParticipation U ∧
    (response U * response U).trace = (Fintype.card ι : ℝ) - 2 * totalParticipation U + realFrobeniusSq ((transition U)ᵀ * transition U) ∧
    diagonalSq (response U) = ∑ j, (1 - columnParticipation U j) ^ 2 := by
  set P := transition U
  set M := Pᵀ * P with hM
  have hMs : Mᵀ = M := by simp [hM, Matrix.transpose_mul]
  have htrM : M.trace = totalParticipation U := by
    simp only [hM, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      totalParticipation, columnParticipation, P, sq]
  have hG : response U = 1 - M := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hG, Matrix.trace_sub, Matrix.trace_one, htrM]
  · have h2 : (M * M).trace = realFrobeniusSq M := by
      have hsym : ∀ i j, M j i = M i j := fun i j => by
        rw [← Matrix.transpose_apply M i j, hMs]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, realFrobeniusSq, sq, hsym]
    rw [hG, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one, htrM, h2]
    ring
  · simp only [diagonalSq, hG, Matrix.sub_apply, Matrix.one_apply_eq, hM, Matrix.mul_apply,
      Matrix.transpose_apply, columnParticipation, P, sq]
