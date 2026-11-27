-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_conj_gaussQ_re_b971a3ac9b26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:12:54.42692+00:00
-- url     : https://prove2.me/submissions/dd8acbe3-6962-4f77-8cfe-7be858100b3d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_gaussQ_78f9ca11f54a
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (z : GaussQ) : (conj ℚ GaussQ z).re = z.re := by
  rw [conj_gaussQ]; simp
end GroundTheory.Heights₂.Theta
