-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_graphPt_injective_c1602eb4686f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:32:42.910963+00:00
-- url     : https://prove2.me/submissions/daa0111f-e3ad-42f9-92e4-1a7b066faad1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula

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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) : Function.Injective (graphPt e F) := by
  intro x y h
  ext i
  have := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z (e.symm (Sum.inl i))) h
  simpa [graphPt] using this
end GroundTheory.Heights₂.Heights
