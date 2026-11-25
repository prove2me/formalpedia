-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_tangent_frame_31c57c5b4317
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:22:58.619797+00:00
-- url     : https://prove2.me/submissions/802ef896-25a0-46bb-a55b-cf6e86b87db4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyTangentGraphDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_frameProjCLM_apply_b4ab43f50eca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology Filter MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
namespace GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
theorem _root_.solution {n : ℕ} (I₀ : Finset (Fin n))
    (L : (I₀ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : Function.Injective L) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      (∀ j ∉ I₀, ∀ v, inner ℂ (b j) (L v) = 0) ∧
      Function.Injective fun v => frameProjCLM b I₀ (L v) := by
  classical
  set T : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := LinearMap.range (L : (I₀ → ℂ) →ₗ[ℂ] _) with hT
  have hfin : Module.finrank ℂ T = Fintype.card I₀ := by
    rw [hT]
    exact (LinearMap.finrank_range_of_inj (f := L.toLinearMap) (by exact hL)).trans
      (Module.finrank_fintype_fun_eq_card ℂ)
  let u : OrthonormalBasis I₀ ℂ T :=
    (stdOrthonormalBasis ℂ T).reindex (Fintype.equivFinOfCardEq hfin.symm).symm
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i =>
    if h : i ∈ I₀ then (u ⟨i, h⟩ : EuclideanSpace ℂ (Fin n)) else 0
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (by rw [finrank_euclideanSpace]) (v := v)
    (s := (I₀ : Set (Fin n))) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi' : i ∈ I₀ := hi
      have hj' : j ∈ I₀ := hj
      have h := orthonormal_iff_ite.1 u.orthonormal ⟨i, hi'⟩ ⟨j, hj'⟩
      simpa [v, hi', hj', Subtype.ext_iff] using h)
  have hbu : ∀ i : I₀, b i = (u i : EuclideanSpace ℂ (Fin n)) := fun i => by
    rw [hb i i.2]
    simp [v, i.2]
  have hTsum : ∀ x : T, (x : EuclideanSpace ℂ (Fin n)) =
      ∑ k : I₀, inner ℂ (b k) (x : EuclideanSpace ℂ (Fin n)) • b k := by
    intro x
    conv_lhs => rw [← u.sum_repr' x]
    simp [hbu, Submodule.coe_inner]
  refine ⟨b, fun j hj w => ?_, fun w w' hww => ?_⟩
  · have hx := hTsum ⟨L w, LinearMap.mem_range_self _ w⟩
    simp only at hx
    rw [hx, inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hjk : j ≠ (k : Fin n) := by
      rintro rfl
      exact hj k.2
    rw [inner_smul_right, b.orthonormal.2 hjk, mul_zero]
  · have h0 : ∀ k : I₀, inner ℂ (b k) (L (w - w')) = 0 := by
      intro k
      have h := congrFun hww k
      simp only [frameProjCLM_apply, frameProj] at h
      rw [map_sub, inner_sub_right, h, sub_self]
    have hx := hTsum ⟨L (w - w'), LinearMap.mem_range_self _ _⟩
    simp only [h0, zero_smul, Finset.sum_const_zero] at hx
    have h1 : w - w' = 0 := hL (by rw [hx, map_zero])
    exact sub_eq_zero.1 h1
end GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
