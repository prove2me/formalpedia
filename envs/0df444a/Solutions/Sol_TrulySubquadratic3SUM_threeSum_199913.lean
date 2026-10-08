-- Prove2me | solution 1 for TrulySubquadratic3SUM.threeSum_199913
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T18:12:34.862387+00:00
-- url     : https://prove2.me/submissions/a3d0c2c8-f211-41d2-902b-e1d8d3b81e05

import Theorems.Thm_TrulySubquadratic3SUM_threeSum_above_15993_8000
import Mathlib.Tactic.NormNum

theorem solution : EndStatement.ThreeSum.SolvedInTime 1.99913 :=
  TrulySubquadratic3SUM.threeSum_above_15993_8000 1.99913 (by norm_num)

#print axioms solution
