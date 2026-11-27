-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isHermitianFor_gramAniso_460f9a93b1ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:33.720873+00:00
-- url     : https://prove2.me/submissions/58598a12-b27b-4535-af65-c10f67484a78

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
theorem _root_.solution : IsHermitianFor (conjHom ℚ GaussQ) gramAniso := by
  unfold IsHermitianFor gramAniso
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  ext i : 1
  fin_cases i <;> simp [conjHom, map_neg, map_ofNat]
end GroundTheory.Heights₂.Theta
