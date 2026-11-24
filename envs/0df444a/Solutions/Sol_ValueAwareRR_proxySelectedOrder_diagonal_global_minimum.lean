-- Prove2me | solution 1 for ValueAwareRR.proxySelectedOrder_diagonal_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:09:49.164003+00:00
-- url     : https://prove2.me/submissions/01c8efe8-0447-4996-9720-95d32a76dcf7

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_diagonalScore_signReverse
import Theorems.Thm_ValueAwareRR_diagonalScore_margin_table

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    diagonalScore m proxySelectedOrder ≤ diagonalScore m o := by
  simp only [proxySelectedOrder]
  rcases o with ⟨r, s⟩
  cases s
  · have hmargin := diagonalScore_margin_table m r
    simp only [proxySelectedOrder] at hmargin
    cases r <;>
      norm_num [diagonalMarginTable] at hmargin ⊢ <;>
      nlinarith [sq_nonneg (m - 2)]
  · rw [← diagonalScore_signReverse m (r, true)]
    norm_num [signReverse]
    have hmargin := diagonalScore_margin_table m r
    simp only [proxySelectedOrder] at hmargin
    cases r <;>
      norm_num [diagonalMarginTable] at hmargin ⊢ <;>
      nlinarith [sq_nonneg (m - 2)]
end ValueAwareRR
