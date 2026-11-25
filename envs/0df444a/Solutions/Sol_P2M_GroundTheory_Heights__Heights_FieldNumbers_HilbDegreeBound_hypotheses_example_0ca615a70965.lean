-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_hypotheses_example_0ca615a70965
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:08.203548+00:00
-- url     : https://prove2.me/submissions/1c92f79d-a280-4812-9e71-bc2c4abdcf0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_bot_projectiveSpace_759c81900cb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eventuallyPoly_projectiveLine_0301a47d8f6f
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
namespace HilbDegreeBound
theorem _root_.solution :
    IsMultiHomogIdeal (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      IsRelevant (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) ∧
      (X () + 1 : MvPolynomial Unit ℚ) ≠ 0 := by
  refine ⟨isMultiHomogIdeal_bot_projectiveSpace 1, isMultiProjPrime_bot.relevant,
    eventuallyPoly_projectiveLine, fun h => ?_⟩
  simpa using congrArg (MvPolynomial.eval fun _ => (0 : ℚ)) h
end HilbDegreeBound
end GroundTheory.Heights₂.Heights.FieldNumbers
