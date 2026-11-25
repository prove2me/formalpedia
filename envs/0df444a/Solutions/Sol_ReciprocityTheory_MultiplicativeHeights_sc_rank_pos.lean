-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_rank_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:46.56427+00:00
-- url     : https://prove2.me/submissions/86b08ef6-e56c-4dc9-9417-041105bb8ff0

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactSecond_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (hN : N ≠ 0) : 0 < finrank K (LinearMap.range N.mulVecLin) := by
  refine Nat.pos_of_ne_zero fun h0 => hN ?_
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := LinearMap.toMatrix'_toLin' N
  rw [Matrix.toLin'_apply', h0, map_zero] at this
  exact this.symm
end ReciprocityTheory.MultiplicativeHeights
