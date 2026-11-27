-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_exists_genericChar_ne_one_31354f66f6ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:12:39.630733+00:00
-- url     : https://prove2.me/submissions/5e385934-a5e1-492b-af11-a0fcf8c64f36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_genericChar_upperTwo_67efdcaf75fa

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
theorem _root_.solution {ψ₀ : AddChar F ℂ} (hψ₀ : ψ₀ ≠ 1) :
    ∃ u, genericChar 2 F ψ₀ u ≠ 1 := by
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ₀
  exact ⟨⟨upperTwo x, upperTwo_mem x⟩, by rwa [genericChar_upperTwo]⟩
end GroundTheory.Heights₂.Theta.FinGL
