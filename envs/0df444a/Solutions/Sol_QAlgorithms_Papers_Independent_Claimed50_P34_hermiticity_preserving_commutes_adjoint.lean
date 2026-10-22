-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P34.hermiticity_preserving_commutes_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:16:17.984212+00:00
-- url     : https://prove2.me/submissions/c98a38b2-3e59-4587-a479-8a3b5419e51c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P34
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P34

theorem solution
    {H1 H2 : Type*}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1] [CompleteSpace H1]
    [TopologicalSpace.SeparableSpace H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    [TopologicalSpace.SeparableSpace H2]
    (V : Submodule ℂ (H2 →L[ℂ] H2))
    (adjointStable : ∀ A : V, A.val.adjoint ∈ V)
    (Phi : V →ₗ[ℂ] (H1 →L[ℂ] H1))
    (preservesHermiticity : ∀ A : V, A.val.adjoint = A.val →
      (Phi A).adjoint = Phi A) :
    ∀ A : V, Phi ⟨A.val.adjoint, adjointStable A⟩ = (Phi A).adjoint := by
  intro A
  set B : V := ⟨A.val.adjoint, adjointStable A⟩ with hB
  -- X = A + B, Y = I • (B - A) are Hermitian
  have hX : (A + B).val.adjoint = (A + B).val := by
    simp [hB, add_comm]
  have hY : ((Complex.I : ℂ) • (B - A)).val.adjoint = ((Complex.I : ℂ) • (B - A)).val := by
    simp only [Submodule.coe_smul, Submodule.coe_sub, hB]
    rw [ContinuousLinearMap.adjoint.map_smulₛₗ, map_sub, ContinuousLinearMap.adjoint_adjoint]
    simp only [Complex.conj_I]
    rw [neg_smul, ← smul_neg, neg_sub]
  have h1 := preservesHermiticity _ hX
  have h2 := preservesHermiticity _ hY
  simp only [map_add, map_smul, map_sub] at h1 h2
  have hadj : ∀ T : H1 →L[ℂ] H1, ContinuousLinearMap.adjoint (Complex.I • T)
      = (-Complex.I) • ContinuousLinearMap.adjoint T := by
    intro T
    rw [ContinuousLinearMap.adjoint.map_smulₛₗ]
    congr 1
    simp
  rw [hadj, map_sub] at h2
  have h2' : (Phi B).adjoint - (Phi A).adjoint = -(Phi B - Phi A) := by
    have := congrArg (fun T => (Complex.I : ℂ) • T) h2
    simp only [smul_smul] at this
    have e : Complex.I * -Complex.I = 1 := by
      rw [mul_neg, Complex.I_mul_I, neg_neg]
    rw [e, one_smul, Complex.I_mul_I, neg_one_smul] at this
    exact this
  have : (2:ℂ) • Phi B = (2:ℂ) • (Phi A).adjoint := by
    rw [two_smul, two_smul]
    have e1 := h1; have e2 := h2'
    calc Phi B + Phi B = ((Phi A).adjoint + (Phi B).adjoint) - ((Phi B).adjoint - (Phi A).adjoint) := by
          rw [e1, e2]; abel
      _ = (Phi A).adjoint + (Phi A).adjoint := by abel
  exact smul_right_injective _ (by norm_num : (2:ℂ) ≠ 0) this
