-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P69.equalNoiseChainComparison
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:35:20.888582+00:00
-- url     : https://prove2.me/submissions/5613de12-ac03-4e6d-9396-0583f3c6f1b2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P69

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intakenext100.P69 in
theorem solution
    (N : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (hlink : xi / ((N : ℝ) + 1) ≤ 1) :
    additiveChainComparisonBound N (fun _ => xi / ((N : ℝ) + 1)) =
      additiveComparisonBound (xi / ((N : ℝ) + 1)) := by
  unfold additiveChainComparisonBound
  exact iInf_const
