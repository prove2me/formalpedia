-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_signature_gramAniso_d74d5f8de813
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:17.751919+00:00
-- url     : https://prove2.me/submissions/4a6ab981-fdf4-4160-8029-90ffdb70ea5f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_gaussValue_diagonal_ee78aa9b998e
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
theorem _root_.solution :
    gaussValue gramAniso ![1, 0] = algebraMap ℚ GaussQ 1 ∧
      gaussValue gramAniso ![0, 1] = algebraMap ℚ GaussQ (-3) ∧ (0 : ℚ) < 1 ∧ (-3 : ℚ) < 0 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [gramAniso, gaussValue_diagonal]
    simp
  · rw [gramAniso, gaussValue_diagonal]
    simp
end GroundTheory.Heights₂.Theta
