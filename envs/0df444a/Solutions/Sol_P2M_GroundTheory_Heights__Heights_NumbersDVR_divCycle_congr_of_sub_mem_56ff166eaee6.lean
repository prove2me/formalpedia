-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:01.62457+00:00
-- url     : https://prove2.me/submissions/85df910b-f1aa-47f3-a395-e524232594a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {s s' : MRing ι R} (h : s - s' ∈ P) : divCycle P s = divCycle P s' := by
  have h1 : s ∈ P ⊔ Ideal.span {s'} := by
    have e : s = (s - s') + s' := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have h2 : s' ∈ P ⊔ Ideal.span {s} := by
    have e : s' = s - (s - s') := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left h)
  have e : P ⊔ Ideal.span {s} = P ⊔ Ideal.span {s'} := le_antisymm
    (sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr h1))
    (sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr h2))
  funext W
  unfold divCycle
  by_cases hc : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W
  · have hc' : W ∈ (P ⊔ Ideal.span {s'}).minimalPrimes ∧ IsRelevant W := e ▸ hc
    rw [dif_pos hc, dif_pos hc', e]
  · have hc' : ¬ (W ∈ (P ⊔ Ideal.span {s'}).minimalPrimes ∧ IsRelevant W) := e ▸ hc
    rw [dif_neg hc, dif_neg hc']
end GroundTheory.Heights₂.Heights.NumbersDVR
