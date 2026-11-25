-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holoContDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:00.294669+00:00
-- url     : https://prove2.me/submissions/b101b055-329d-46bc-afbe-dfe0448e047b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExistsClmOfI
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffAtComplex
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holoDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open Metric Set Filter Topology Complex
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : HoloContDiffStatement := by
  intro n Ω f hΩ hf
  rw [contDiffOn_infty]
  intro k
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨hf, fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_clm_apply]
    intro v
    exact ih _ (holoDeriv n Ω f hΩ hf v)
end ReciprocityTheory.L2DbarEstimates.C
