-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.boxvol.sum_range_succ_mul_sub_pred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:42:10.149601+00:00
-- url     : https://prove2.me/submissions/462a6cb6-ed93-4537-809b-afd9a0921f4f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_BoxVolumes_SumRangeSuccMulSubPred

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.boxvol
namespace PositivityTheory.Rg.Rs.boxvol
theorem _root_.solution (y : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ range (n + 1), (r : ℝ) * (y (r - 1) - y r) = ∑ i ∈ range n, y i - n * y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
end PositivityTheory.Rg.Rs.boxvol
