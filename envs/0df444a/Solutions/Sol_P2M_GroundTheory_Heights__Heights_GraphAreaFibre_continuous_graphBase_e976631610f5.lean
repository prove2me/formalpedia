-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaFibre_continuous_graphBase_e976631610f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:03.857813+00:00
-- url     : https://prove2.me/submissions/8a939836-e746-4202-aa24-aff0401dc83f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaMultiplicityWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGraphAreaFibre

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
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace GraphAreaFibre
theorem _root_.solution {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) :
    Continuous (graphBase e : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin d)) := by
  unfold graphBase
  fun_prop
end GraphAreaFibre
end GroundTheory.Heights₂.Heights
