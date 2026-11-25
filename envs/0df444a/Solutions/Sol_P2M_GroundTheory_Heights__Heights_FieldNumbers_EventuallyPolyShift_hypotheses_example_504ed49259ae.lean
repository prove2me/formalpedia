-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_EventuallyPolyShift_hypotheses_example_504ed49259ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:12.75382+00:00
-- url     : https://prove2.me/submissions/c8335922-9a3d-465f-a43d-6e8a1e451e3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eventuallyPoly_projectiveLine_0301a47d8f6f


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
namespace EventuallyPolyShift
theorem _root_.solution :
    EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) :=
  eventuallyPoly_projectiveLine
end EventuallyPolyShift
end GroundTheory.Heights₂.Heights.FieldNumbers
