-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_gaussValue_diagonal_ee78aa9b998e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:37.019405+00:00
-- url     : https://prove2.me/submissions/0dd40fb1-a943-4a02-bc03-0070ec9fec08

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
theorem _root_.solution (d : Fin 2 → GaussQ) (x : Fin 2 → GaussQ) :
    gaussValue (Matrix.diagonal d) x =
      d 0 * (x 0 * conj ℚ GaussQ (x 0)) + d 1 * (x 1 * conj ℚ GaussQ (x 1)) := by
  simp only [gaussValue, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring
end GroundTheory.Heights₂.Theta
