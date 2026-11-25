-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_herm_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:48:22.276881+00:00
-- url     : https://prove2.me/submissions/7c2e3d5f-529a-4d77-9cd3-717b0a0d737d

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : Mᴴ = M) (v w : Fin r → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by
  rw [star_mulVec, hM, dotProduct_mulVec]
end ReciprocityTheory.MultiplicativeHeights
