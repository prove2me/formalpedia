-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalDigitSpan.menu_admissible_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:44:13.27118+00:00
-- url     : https://prove2.me/submissions/1a60cc9e-14b0-4734-ae5d-224ef700c90c

import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_physical_span_iff
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightStoredSpan_program_length
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightStoredSpan.program_length
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] {J : ℕ}
variable {E : Type*} [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
namespace ThreeSum.TernaryPhysicalDigitSpan
theorem _root_.solution (ℓ : E →ₗ[K] K) (rows : List (Fin J → K)) (seed : E×E) :
    seed∈TernaryOriginalRowMenu.admissible (J+2) ℓ (forbidden rows) ↔
      physicalDigits (TernaryOriginalRowMenu.seedRow (J+2) ℓ seed)∉oldSpan (rows.map (reversal J)) := by
  simp only [TernaryOriginalRowMenu.admissible,Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr (physical_span_iff rows _).symm
end ThreeSum.TernaryPhysicalDigitSpan
