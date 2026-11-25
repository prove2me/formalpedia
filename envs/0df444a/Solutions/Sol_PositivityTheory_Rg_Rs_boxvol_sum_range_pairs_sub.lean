-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.boxvol.sum_range_pairs_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:18.547111+00:00
-- url     : https://prove2.me/submissions/ffc190df-7a67-4dfe-a9cb-3ea61438a313

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_BoxVolumes_SumRangeSuccMulSubPred
import Theorems.Thm_PositivityTheory_Rg_Rs_boxvol_sum_range_succ_mul_sub_pred

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
    ∑ j ∈ range n, ∑ i ∈ range j, (y i - y j)
      = ∑ r ∈ range n, ((r : ℝ) * ((n : ℝ) - r)) * (y (r - 1) - y r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ r ∈ range (n + 1), ((r : ℝ) * (((n + 1 : ℕ) : ℝ) - r)) * (y (r - 1) - y r)
        = ∑ r ∈ range (n + 1), ((r : ℝ) * ((n : ℝ) - r)) * (y (r - 1) - y r)
          + ∑ r ∈ range (n + 1), (r : ℝ) * (y (r - 1) - y r) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun r _ => ?_
      push_cast
      ring
    rw [h1, sum_range_succ_mul_sub_pred, sum_range_succ, ih, sum_range_succ _ n]
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring
end PositivityTheory.Rg.Rs.boxvol
