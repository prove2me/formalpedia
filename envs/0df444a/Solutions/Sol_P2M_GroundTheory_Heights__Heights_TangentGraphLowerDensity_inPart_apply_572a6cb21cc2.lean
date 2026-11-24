-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_apply_572a6cb21cc2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:57.569024+00:00
-- url     : https://prove2.me/submissions/70f45790-cc03-49ff-bca5-5f139ef060dc

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
    (z : EuclideanSpace ℂ (Fin n)) (i : I) :
    TangentGraphLowerDensity.inPart b I z i = inner ℂ (b i) z := by
  simp [TangentGraphLowerDensity.inPart]
end TangentGraphLowerDensity
end GroundTheory.Heights₂.Heights
