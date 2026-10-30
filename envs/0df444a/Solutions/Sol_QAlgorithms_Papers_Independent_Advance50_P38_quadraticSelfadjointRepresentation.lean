-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.quadraticSelfadjointRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:19:42.557296+00:00
-- url     : https://prove2.me/submissions/ecfd2013-0548-4426-8bad-0437b3e0c18d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

lemma sa_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S T : H →L[ℝ] H) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (h : ∀ v, inner ℝ v (S v) = inner ℝ v (T v)) : S = T := by
  have hsym : ((S - T : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := by
    have := (hS.sub hT)
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp this)
  have h0 := (LinearMap.IsSymmetric.inner_map_self_eq_zero hsym).mp (by
    intro x
    simp only [ContinuousLinearMap.coe_coe, sub_apply, inner_sub_left]
    rw [real_inner_comm x (S x), real_inner_comm x (T x)]
    have := h x
    linarith)
  ext x
  have := congrArg (fun f => f x) h0
  simpa [sub_eq_zero] using this

lemma sa_exists {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Bf : H →L[ℝ] H →L[ℝ] ℝ) (hsymm : ∀ v w, Bf v w = Bf w v) :
    ∃ T : H →L[ℝ] H, IsSelfAdjoint T ∧ ∀ v, inner ℝ v (T v) = Bf v v := by
  let T : H →L[ℝ] H := InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) Bf
  have hT : ∀ v w, inner ℝ (T v) w = Bf v w := by
    intro v w
    exact InnerProductSpace.continuousLinearMapOfBilin_apply (𝕜 := ℝ) Bf v w
  refine ⟨T, ?_, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro v w
    simp only [ContinuousLinearMap.coe_coe]
    rw [hT, real_inner_comm, hT, hsymm]
  · intro v
    rw [real_inner_comm, hT]

end

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38 in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (beta : H → ℝ)
    (hbeta : IsBoundedQuadratic beta) :
    ∃! B : H →L[ℝ] H, IsSelfAdjoint B ∧ ∀ v, inner ℝ v (B v) = beta v := by
  obtain ⟨Bf, hsymm, hb⟩ := hbeta
  obtain ⟨T, hTs, hTq⟩ := sa_exists Bf hsymm
  refine ⟨T, ⟨hTs, fun v => by rw [hTq, hb]⟩, ?_⟩
  rintro S ⟨hSs, hSq⟩
  exact sa_unique S T hSs hTs (fun v => by rw [hSq, hTq, hb])
