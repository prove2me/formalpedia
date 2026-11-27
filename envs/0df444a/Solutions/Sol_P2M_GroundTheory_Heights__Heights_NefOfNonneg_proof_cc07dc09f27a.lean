-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NefOfNonneg_proof_cc07dc09f27a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:25.508623+00:00
-- url     : https://prove2.me/submissions/3e932441-f37f-42b3-b843-63360c0e79ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PNefOfNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_one_nonneg_729cfb3b0c67

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
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights
namespace NefOfNonneg
theorem _root_.solution : NefOfNonneg.Statement := by
  intro K _ ι _ P a ha W _ _ _ _
  exact NefOfNonnegAlt.geoNum_one_nonneg W a ha
end NefOfNonneg
end GroundTheory.Heights₂.Heights
