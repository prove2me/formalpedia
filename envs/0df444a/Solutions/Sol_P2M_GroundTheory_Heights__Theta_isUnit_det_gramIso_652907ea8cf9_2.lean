-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Theta_isUnit_det_gramIso_652907ea8cf9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:14.732884+00:00
-- url     : https://prove2.me/submissions/d8925e6e-144b-4451-9bb2-f49d8674b7c1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
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
theorem _root_.solution : IsUnit gramIso.det := by
  rw [gramIso, Matrix.det_diagonal, Fin.prod_univ_two]
  simp
end GroundTheory.Heights₂.Theta
