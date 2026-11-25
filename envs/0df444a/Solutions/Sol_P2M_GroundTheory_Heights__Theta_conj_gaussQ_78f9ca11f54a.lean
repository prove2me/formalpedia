-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_conj_gaussQ_78f9ca11f54a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:15.604621+00:00
-- url     : https://prove2.me/submissions/83d54983-949e-4431-bc7c-9557d3c7e7de

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_gauss_algebraMap_re_46418eb09d11
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_gauss_algebraMap_im_9a09597e1d8f
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_trace_gaussQ_11da65445202
import Theorems.Thm_GroundTheory_Automorphic_conj_apply
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
theorem _root_.solution (z : GaussQ) : conj ℚ GaussQ z = star z := by
  rw [conj_apply, trace_gaussQ]
  ext
  · simp only [QuadraticAlgebra.re_sub, gauss_algebraMap_re, QuadraticAlgebra.re_star]; ring
  · simp only [QuadraticAlgebra.im_sub, gauss_algebraMap_im, QuadraticAlgebra.im_star]; ring
end GroundTheory.Heights₂.Theta
