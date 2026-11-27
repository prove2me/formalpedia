-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaneSliceMass_line_ae198cc5be7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:25.216122+00:00
-- url     : https://prove2.me/submissions/94f3548d-f1c3-4a55-90d4-1fc20f0eb606

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaneSliceMass

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PlaneSliceMass
theorem _root_.solution (H : PlaneSliceMass.Statement) : LineSliceMass.Statement := H 1
end PlaneSliceMass
end GroundTheory.Heights₂.Heights
