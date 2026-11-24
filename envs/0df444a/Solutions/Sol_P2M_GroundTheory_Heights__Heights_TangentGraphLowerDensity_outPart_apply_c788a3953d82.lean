-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_outPart_apply_c788a3953d82
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:45.795215+00:00
-- url     : https://prove2.me/submissions/31cce575-77a8-49e2-983d-9603c0a8f49c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTangentGraphLowerDensity

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
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TangentGraphLowerDensity
theorem _root_.solution {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : {j : Fin n // j ∉ I}) :
    TangentGraphLowerDensity.outPart b I z j = inner ℂ (b j) z := by
  simp [TangentGraphLowerDensity.outPart]
end TangentGraphLowerDensity
end GroundTheory.Heights₂.Heights
