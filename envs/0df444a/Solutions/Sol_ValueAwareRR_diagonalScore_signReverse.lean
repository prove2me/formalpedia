-- Prove2me | solution 1 for ValueAwareRR.diagonalScore_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:00:24.463622+00:00
-- url     : https://prove2.me/submissions/73d678a8-da5b-49e7-ae4a-455a88d5b73a

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_prefixOne_signReverse
import Theorems.Thm_ValueAwareRR_prefixTwo_signReverse
import Theorems.Thm_ValueAwareRR_prefixThree_signReverse

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    diagonalScore m (signReverse o) = diagonalScore m o := by
  simp only [diagonalScore, prefixOne_signReverse, prefixTwo_signReverse,
    prefixThree_signReverse]
  ring
end ValueAwareRR
