-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Theta_isHermitianFor_gramIso_9bf32f5a6198
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:36.502239+00:00
-- url     : https://prove2.me/submissions/55a0a916-58cf-4ab1-ac89-a174abc29f31

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
theorem _root_.solution : IsHermitianFor (conjHom ℚ GaussQ) gramIso := by
  unfold IsHermitianFor gramIso
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  ext i : 1
  fin_cases i <;> simp [conjHom, map_neg]
end GroundTheory.Heights₂.Theta
