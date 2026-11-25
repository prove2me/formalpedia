-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_proof_d70ea9f87160
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:49.895084+00:00
-- url     : https://prove2.me/submissions/02fed58c-f2ab-439c-8f98-64a5cd091ce5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_intersectionNumber_baseChange_2de51cffb9c7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (_h : LocalRingHypotheses.Statement) : PlaceMaps.Statement := intersectionNumber_baseChange
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
