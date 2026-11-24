-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_mem_not_mem_9fb2fa7ea052
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:36.650794+00:00
-- url     : https://prove2.me/submissions/6e19db1a-6ef7-4776-8f3f-42741b905c22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {H H' : Ideal (MRing ι R)} (hH' : IsMultiHomogIdeal H')
    (h : ¬ H' ≤ H) : ∃ (x : MRing ι R) (e : K → ℕ), IsMultiHomog x e ∧ x ∈ H' ∧ x ∉ H := by
  obtain ⟨y, hy, hyH⟩ := Set.not_subset.mp h
  obtain ⟨e, he⟩ := exists_component_not_mem hyH
  exact ⟨_, e, weightedHomogeneousComponent_isWeightedHomogeneous _ _, hH' y hy e, he⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
