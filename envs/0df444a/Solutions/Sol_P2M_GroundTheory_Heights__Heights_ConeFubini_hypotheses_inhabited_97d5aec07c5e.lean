-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFubini_hypotheses_inhabited_97d5aec07c5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:19.732144+00:00
-- url     : https://prove2.me/submissions/1f756afb-c0a2-46f3-b5d5-f06b962af38b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ConeFubini
theorem _root_.solution :
    IsFiniteMeasure (Measure.dirac (0 : EuclideanSpace ℂ (Fin 1))) ∧
      Measurable (Function.uncurry fun (_ : Fin 1 → ℂ) (_ : EuclideanSpace ℂ (Fin 1)) => (0 : ℝ)) :=
  ⟨inferInstance, measurable_const⟩
end ConeFubini
end GroundTheory.Heights₂.Heights
