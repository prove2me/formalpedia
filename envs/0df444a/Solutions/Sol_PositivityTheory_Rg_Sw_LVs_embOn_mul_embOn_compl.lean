-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.embOn_mul_embOn_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:01.270113+00:00
-- url     : https://prove2.me/submissions/f58bd7c1-e248-49ad-a76b-a8e6bb18e8de

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (j : ℕ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) :
    embOn (blkB j) S * embOn (blkA j) T = 0 ∧ embOn (blkA j) T * embOn (blkB j) S = 0 := by
  constructor
  · ext a c
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [embOn]
    split_ifs with h1 h2
    · exact absurd h2.1 (by simpa [blkB] using h1.2)
    · simp
    · simp
    · simp
  · ext a c
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [embOn]
    split_ifs with h1 h2
    · exact absurd h1.2 (by simpa [blkB] using h2.1)
    · simp
    · simp
    · simp
end PositivityTheory.Rg.Sw.LVs
