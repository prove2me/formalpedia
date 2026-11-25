-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_range_8f1b7a26fca2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:41.495869+00:00
-- url     : https://prove2.me/submissions/ea707361-b9d9-4e1e-83ea-dccd4a01daa8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGridSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_antidiagonal_c2622c68f772

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Finset Filter Asymptotics
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace GridSum
theorem _root_.solution (n i j : ℕ) :
    ∑ a ∈ range n, a.choose i * (n - 1 - a).choose j = n.choose (i + j + 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [← GridSum.choose_antidiagonal m i j, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
end GridSum
end GroundTheory.Heights₂.Heights.HilbertSamuel
