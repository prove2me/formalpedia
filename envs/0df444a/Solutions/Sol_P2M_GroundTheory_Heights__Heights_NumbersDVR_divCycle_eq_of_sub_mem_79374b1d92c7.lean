-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_sub_mem_79374b1d92c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:35.800796+00:00
-- url     : https://prove2.me/submissions/2233a136-b758-46b6-8492-7c6cae6c34bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} {x y : MRing ι R} (h : x - y ∈ P) :
    divCycle P x = divCycle P y := by
  have hI : P ⊔ Ideal.span {x} = P ⊔ Ideal.span {y} := by
    have key : ∀ {x' y' : MRing ι R}, x' - y' ∈ P → P ⊔ Ideal.span {x'} ≤ P ⊔ Ideal.span {y'} := by
      intro x' y' h'
      refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : x' = (x' - y') + y' := by ring
      rw [e]
      exact Submodule.add_mem_sup h' (Ideal.subset_span rfl)
    refine le_antisymm (key h) (key ?_)
    rw [← neg_sub]
    exact P.neg_mem h
  funext W
  unfold divCycle
  by_cases hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W
  · have hW' : W ∈ (P ⊔ Ideal.span {y}).minimalPrimes ∧ IsRelevant W := hI ▸ hW
    rw [dif_pos hW, dif_pos hW']
    simp only [hI]
  · have hW' : ¬ (W ∈ (P ⊔ Ideal.span {y}).minimalPrimes ∧ IsRelevant W) := hI ▸ hW
    rw [dif_neg hW, dif_neg hW']
end GroundTheory.Heights₂.Heights.NumbersDVR
