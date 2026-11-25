-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_coneSet_iff_pointOfL_9f474107b28f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:52.573823+00:00
-- url     : https://prove2.me/submissions/e0a82904-0306-4c5b-b3e2-be75843b80a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass

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
open MvPolynomial MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : y ∈ coneSet h J ↔ h.pointOfL y ∈ zeroSetEuc J :=
  Iff.rfl
end GroundTheory.Heights₂.Heights
