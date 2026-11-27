-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_proof_f3cd81616161
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:05.390353+00:00
-- url     : https://prove2.me/submissions/41022b4f-b4b9-4dd2-96ff-e2d4d1e9f4fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PAwayHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PChartBundlesAgree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_lat_le_5aaf4adeea9e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
namespace ChartBundlesAgree
theorem _root_.solution (hHOI : HeightOneIntersection.Statement) :
    ChartBundlesAgree.Statement := by
  intro o _ Ω _ _ τ x r E _ _ B B' i hi hN hIC h1 h2 hq
  exact le_antisymm
    (ChartBundlesAgree.lat_le hHOI B B' i hi hN hIC h1 fun q hq' hq1 v => (hq q hq' hq1 v).1)
    (ChartBundlesAgree.lat_le hHOI B' B i hi hN hIC h2 fun q hq' hq1 v => (hq q hq' hq1 v).2)
end ChartBundlesAgree
end GroundTheory.Heights₂.Heights.Model
