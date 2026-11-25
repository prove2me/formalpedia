-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_genericChar_upperTwo_67efdcaf75fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:52.461742+00:00
-- url     : https://prove2.me/submissions/25bebde5-a8a3-4c5f-ad14-d6da0c53d397

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FinGL
open Matrix
noncomputable section
variable {n : ℕ} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Theta.FinGL
theorem _root_.solution (ψ₀ : AddChar F ℂ) (x : F) :
    genericChar 2 F ψ₀ ⟨upperTwo x, upperTwo_mem x⟩ = ψ₀ x := by
  simp [genericChar, superdiagSum, Fin.sum_univ_two, upperTwo]
end GroundTheory.Heights₂.Theta.FinGL
