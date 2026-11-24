-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBase_hypotheses_example_77f0c5696e4b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:38.689549+00:00
-- url     : https://prove2.me/submissions/cc687dcd-6db4-4d04-a66c-ba176b7db000

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
namespace IntNumBase
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 0) ℚ)) = 0 := by
  refine ⟨isMultiProjPrime_bot, ?_⟩
  rw [relDim_projectiveSpace]
  rfl
end IntNumBase
end GroundTheory.Heights₂.Heights.FieldNumbers
