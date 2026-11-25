-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_gauss_algebraMap_re_46418eb09d11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:14.779147+00:00
-- url     : https://prove2.me/submissions/cd11901a-35ff-4c22-9233-d6b8301bd2a4

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
theorem _root_.solution (q : ℚ) : (algebraMap ℚ GaussQ q).re = q := rfl
end GroundTheory.Heights₂.Theta
