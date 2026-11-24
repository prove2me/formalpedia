-- Prove2me | solution 1 for PI.QnHermHaar.hermFromSteps_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:43:51.859917+00:00
-- url     : https://prove2.me/submissions/cc43645f-b324-419d-94d2-3fc8304e82ad

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development

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
    (hY : YbRel) (hX : XbRel) (hH : HmFacts) (hG : Glue) : HermFromSteps := by
  intro hRd hSM hCC hMV hMC hYL hGl hEP
  exact hG (hA hSM hCC hMV hMC) hT (hE hRd hEP hT hI) hM hI hY hX hH hEP hGl hYL
end PI.QnHermHaar
