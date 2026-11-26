-- Prove2me | solution 1 for Sendov.tail1_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:51:15.566873+00:00
-- url     : https://prove2.me/submissions/7d667032-ef18-4f6a-a417-feb43e1ab70a

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution {j α : ℝ} (hj : 0 ≤ j) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    108150000 * (100 + j - 2 * α) ^ 2
      ≤ 101 * (100 - 2 * α) ^ 2 * ((100 + j) * (103 + j) * (105 + j)) := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have hj2 : (0 : ℝ) ≤ j ^ 2 := sq_nonneg j
  have hj3 : (0 : ℝ) ≤ j ^ 3 := pow_nonneg hj 3
  have h0 : (0 : ℝ) ≤ 1010000 * j ^ 3 + 202930000 * j ^ 2 + 10301150000 * j + 10815000000 := by
    linarith
  have h1 : (0 : ℝ) ≤ 1333200 * j ^ 3 + 194325600 * j ^ 2 + 6243318000 * j + 14275800000 := by
    linarith
  have h2 : (0 : ℝ) ≤ 439956 * j ^ 3 + 27356448 * j ^ 2 - 366591060 * j + 4711014000 := by
    nlinarith [sq_nonneg (4559408 * j - 30549255), hj3]
  have hid : (17 : ℝ) ^ 2 *
      (101 * (100 - 2 * α) ^ 2 * ((100 + j) * (103 + j) * (105 + j))
        - 108150000 * (100 + j - 2 * α) ^ 2)
      = (1010000 * j ^ 3 + 202930000 * j ^ 2 + 10301150000 * j + 10815000000) * (17 - α) ^ 2
        + (1333200 * j ^ 3 + 194325600 * j ^ 2 + 6243318000 * j + 14275800000)
            * (α * (17 - α))
        + (439956 * j ^ 3 + 27356448 * j ^ 2 - 366591060 * j + 4711014000) * α ^ 2 := by
    ring
  nlinarith [mul_nonneg h0 (sq_nonneg (17 - α)), mul_nonneg h1 (mul_nonneg hα hu),
    mul_nonneg h2 (sq_nonneg α)]
end Sendov
