-- Prove2me | solution 1 for PI.QnHermHaar.qnHermHaar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:25.626359+00:00
-- url     : https://prove2.me/submissions/14f0d3a0-c16a-4cbd-a347-ea352ed4d9ec

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Theorems.Thm_PI_QnHermHaar_hermFromSteps_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.QnHermHaar
theorem _root_.solution (hA : HermAlgFrom) (hE : EabAdjFrom) (hT : EabTest) (hM : MulTest) (hI : TestInt)
    (hY : YbRel) (hX : XbRel) (hH : HmFacts) (hG : Glue) :
    RdSkew → StarMinor → ContractionsCovariant → MoveVec → MoveCov → YLeibniz → EabGlLev → EabPres → HermHaar :=
  hermFromSteps_of hA hE hT hM hI hY hX hH hG
end PI.QnHermHaar
