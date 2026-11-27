-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_conj_gaussQ_im_0bf2c7b57145
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:42.916644+00:00
-- url     : https://prove2.me/submissions/b484f96f-8f45-4ced-bd24-510d5d7435b1

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
theorem _root_.solution (z : GaussQ) : (conj ℚ GaussQ z).im = -z.im := by
  first | (change (conjLinear ℚ GaussQ z).im = -z.im; simp [conjLinear]; done) | (change (QuadraticAlgebra.im (star z)) = _; simp) | (simp [conj, conjLinear]; done) | (simp [conj, conjLinear]; rfl) | exact QuadraticAlgebra.im_star z



