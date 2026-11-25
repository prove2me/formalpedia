-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaFibre_differentiableAt_graphPt_4ee4476b47eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:04.879005+00:00
-- url     : https://prove2.me/submissions/a42100da-6841-47d0-be2b-6f4f63d968ee

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
theorem _root_.solution {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hΦ : DifferentiableAt ℂ Φ x) : DifferentiableAt ℂ (graphPt e Φ) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => Φ y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hΦ i
end GraphAreaFibre
end GroundTheory.Heights₂.Heights
