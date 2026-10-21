-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P03.finite_vectorization_phiPlus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:48:30.031984+00:00
-- url     : https://prove2.me/submissions/06a631b1-fcc2-44f7-801d-268688a633f9

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)


open QAlgorithms.Papers.Independent.Renew46.P03
open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

theorem g64v_main {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ H) (A : H →L[ℂ] H) :
    finiteVectorization b A =
      completedTensorAction (ContinuousLinearMap.id ℂ H) A (unnormalizedBasisTensor b) := by
  simp only [finiteVectorization, unnormalizedBasisTensor, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold completedTensorAction tensorVector
  rw [ContinuousLinearMap.extend_eq (h_dense := UniformSpace.Completion.denseRange_coe)
    (h_e := UniformSpace.Completion.isUniformInducing_coe _)]
  simp

/-- Equation (2.1), PDF p.9: finite vectorization is the action of I tensor A
on unnormalized phi_plus. The result includes dimension zero. -/
theorem solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ H) (A : H →L[ℂ] H) :
    finiteVectorization b A =
      completedTensorAction (ContinuousLinearMap.id ℂ H) A (unnormalizedBasisTensor b) := by
  exact g64v_main b A


end
