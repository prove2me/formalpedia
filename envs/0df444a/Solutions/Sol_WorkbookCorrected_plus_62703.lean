-- Prove2me | solution 1 for WorkbookCorrected.plus_62703
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:28:29.053748+00:00
-- url     : https://prove2.me/submissions/24ee3948-a187-4f1e-881b-ba9c464fbb33

import Mathlib

theorem solution (n : ℕ) : ∑ r ∈ Finset.range (n+1), Nat.choose n r = 2^n :=
  Nat.sum_range_choose n
