-- Prove2me | solution 1 for ValueAwareRR.maxPrefixScore_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:55:02.605817+00:00
-- url     : https://prove2.me/submissions/9e161629-479f-466d-b7e7-1075162d3f31

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) (r : Representative) :
    maxPrefixScore m (r, false) = maxPrefixTable m r := by
  cases r <;>
    simp [maxPrefixScore, prefixOne, prefixTwo, prefixThree, orderedResidual,
      residual, orderAt, representativeOrder, familyA, familyB, maxPrefixTable] <;>
    ring_nf
  all_goals
    repeat' first
      | rw [abs_of_nonneg (by nlinarith)]
      | rw [abs_of_nonpos (by nlinarith)]
    simp only [max_def]
    split_ifs <;> nlinarith
end ValueAwareRR
