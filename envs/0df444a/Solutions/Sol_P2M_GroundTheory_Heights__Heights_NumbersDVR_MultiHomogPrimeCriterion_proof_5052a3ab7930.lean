-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_proof_5052a3ab7930
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:38.18589+00:00
-- url     : https://prove2.me/submissions/1f0e01a0-ddba-47db-91fe-8085427ab33c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_surjective_74d3e094c6c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_component_lexDeg_5586e765bcb9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_isMultiHomog_of_lex_e97f02c5fe46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_coe_decompose_3592f7bbfe4c

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
open GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
theorem _root_.solution : MultiHomogPrimeCriterion.Statement := by
  intro R _ K _ _ ι Q hQ hne hform
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := weightedHomogeneousSubmodule R (lexDeg ∘ blockWeight ι)) ?_ hne ?_
  · intro i r hr
    obtain ⟨b, rfl⟩ := lexDeg_surjective i
    rw [coe_decompose, component_lexDeg]
    exact hQ r hr b
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    obtain ⟨sa, ha⟩ := isMultiHomog_of_lex hx
    obtain ⟨sb, hb⟩ := isMultiHomog_of_lex hy
    exact hform x y sa sb ha hb hxy
end GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
