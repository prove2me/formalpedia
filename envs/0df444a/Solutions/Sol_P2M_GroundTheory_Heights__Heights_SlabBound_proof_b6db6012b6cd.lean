-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SlabBound_proof_b6db6012b6cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:04.86158+00:00
-- url     : https://prove2.me/submissions/48a1411f-148a-4a3d-b064-8802cdb67593

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AffineOfCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSlabBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SlabBound_affine_9aab2d8bdd67


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
namespace GroundTheory.Heights₂.Heights
namespace SlabBound
theorem _root_.solution : SlabBound.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine
end SlabBound
end GroundTheory.Heights₂.Heights
