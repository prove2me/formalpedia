-- Prove2me | solution 1 for SumProduct.goldenRatio_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:21:49.038322+00:00
-- url     : https://prove2.me/submissions/7531f3bc-672f-4da3-803c-bc2d79213160

import Mathlib
import Definitions.Def_SumProduct_GoldenRatio

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution : (8 : ℝ) / 5 ≤ Real.goldenRatio := by
  have h5 : (11 : ℝ) / 5 ≤ Real.sqrt 5 := by
    rw [show (11 : ℝ) / 5 = Real.sqrt ((11 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  change (8 : ℝ) / 5 ≤ (1 + Real.sqrt 5) / 2
  linarith
end SumProduct
