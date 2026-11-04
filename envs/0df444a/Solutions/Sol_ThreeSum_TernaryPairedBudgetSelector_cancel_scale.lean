-- Prove2me | solution 1 for ThreeSum.TernaryPairedBudgetSelector.cancel_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:35.168982+00:00
-- url     : https://prove2.me/submissions/1a9ab987-4abc-489e-9b71-ef799a335b30

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.TernaryPairedBudgetSelector
theorem _root_.solution (a b s value budget : ℕ) (hs : 0<s)
    (h : a*(s*value)≤s*b*budget) : a*value≤b*budget := by
  apply Nat.le_of_mul_le_mul_left (c := s) ?_ hs
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h
end ThreeSum.TernaryPairedBudgetSelector
