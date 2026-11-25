-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_gauss_algebraMap_im_9a09597e1d8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:06.093227+00:00
-- url     : https://prove2.me/submissions/f4cd7075-e5ff-4480-aaa3-da187f8ef3a0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (q : ℚ) : (algebraMap ℚ GaussQ q).im = 0 := rfl
end GroundTheory.Heights₂.Theta
