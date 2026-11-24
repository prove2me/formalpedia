-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ProductWithProjectiveSpace_hypotheses_example_bd159c78b846
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:39.417223+00:00
-- url     : https://prove2.me/submissions/35c34cc4-941a-4521-be14-e3f1c15dabb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_projectiveSpace_e590f169e76b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ProductWithProjectiveSpace
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) = (0 : ℕ) ∧ 0 + 1 = 0 + 1 :=
  ⟨isMultiProjPrime_bot, relDim_projectiveSpace 0, rfl⟩
end ProductWithProjectiveSpace
end GroundTheory.Heights₂.Heights.FieldNumbers
