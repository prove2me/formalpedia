-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_imageArith_534826b29d9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:22:50.057467+00:00
-- url     : https://prove2.me/submissions/4166ba67-24cb-44ee-8289-b53e3c4912c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImageArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImageArithClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_proof_71d40a4eb56d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ImageArith_of_found_2974011bfbbf


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
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement :=
  ImageArith.of_found BlockTrdeg.proof
end GroundTheory.Heights₂.Heights
