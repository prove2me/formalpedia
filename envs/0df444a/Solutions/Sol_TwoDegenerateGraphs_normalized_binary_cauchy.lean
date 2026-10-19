-- Prove2me | solution 1 for TwoDegenerateGraphs.normalized_binary_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/222a35dd-a489-40a8-8af9-26e4c344bf5d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (a b x y : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    a * x + b * y ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  have hrad : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hroot := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have hsquare := Real.sq_sqrt hrad
  have hidentity :
      (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
        (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    ring
  rw [hab, one_mul] at hidentity
  nlinarith [sq_nonneg (a * y - b * x)]
end TwoDegenerateGraphs
