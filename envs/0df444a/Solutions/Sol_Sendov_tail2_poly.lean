-- Prove2me | solution 1 for Sendov.tail2_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:51:17.954145+00:00
-- url     : https://prove2.me/submissions/1eb66268-ca40-40b6-b004-6623d226fd8c

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution {k α : ℝ} (hk : 0 ≤ k) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    12 * (101 + k - 2 * α) ^ 2 * (102 + k) * (100 + k) ^ 2
      ≤ 13 * (100 + k - 2 * α) ^ 2 * (99 + k) * (101 + k) ^ 2 := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have hk2 : (0 : ℝ) ≤ k ^ 2 := sq_nonneg k
  have hk3 : (0 : ℝ) ≤ k ^ 3 := pow_nonneg hk 3
  have hk4 : (0 : ℝ) ≤ k ^ 4 := pow_nonneg hk 4
  have hk5 : (0 : ℝ) ≤ k ^ 5 := pow_nonneg hk 5
  have h0 : (0 : ℝ) ≤ k ^ 5 + 465 * k ^ 4 + 85927 * k ^ 3 + 7878063 * k ^ 2
      + 357802600 * k + 6426630000 := by linarith
  have h1 : (0 : ℝ) ≤ 2 * k ^ 5 + 862 * k ^ 4 + 146218 * k ^ 3 + 12147842 * k ^ 2
      + 491029284 * k + 7642508400 := by linarith
  have h2 : (0 : ℝ) ≤ k ^ 5 + 397 * k ^ 4 + 61447 * k ^ 3 + 4603863 * k ^ 2
      + 165348456 * k + 2243200572 := by linarith
  have hid : (17 : ℝ) ^ 2 *
      (13 * (100 + k - 2 * α) ^ 2 * (99 + k) * (101 + k) ^ 2
        - 12 * (101 + k - 2 * α) ^ 2 * (102 + k) * (100 + k) ^ 2)
      = (k ^ 5 + 465 * k ^ 4 + 85927 * k ^ 3 + 7878063 * k ^ 2 + 357802600 * k + 6426630000)
          * (17 - α) ^ 2
        + (2 * k ^ 5 + 862 * k ^ 4 + 146218 * k ^ 3 + 12147842 * k ^ 2 + 491029284 * k
            + 7642508400) * (α * (17 - α))
        + (k ^ 5 + 397 * k ^ 4 + 61447 * k ^ 3 + 4603863 * k ^ 2 + 165348456 * k
            + 2243200572) * α ^ 2 := by
    ring
  nlinarith [mul_nonneg h0 (sq_nonneg (17 - α)), mul_nonneg h1 (mul_nonneg hα hu),
    mul_nonneg h2 (sq_nonneg α)]
end Sendov
