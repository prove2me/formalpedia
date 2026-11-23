-- Prove2me | solution 1 for SumProduct.floor_ratio_lt_goldenRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:47:49.967531+00:00
-- url     : https://prove2.me/submissions/9f29f87e-c706-473f-b8cb-2474a9e25de6

import Mathlib
import Definitions.Def_SumProduct_GoldenRatio
import Theorems.Thm_SumProduct_goldenRatio_ge

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {X ε : ℝ} (hX : 2 ≤ X) (hε0 : 0 < ε) (hε : ε ≤ 3 / 20) :
    ((⌊X⌋₊ : ℝ) + ε * X) / ((⌊X⌋₊ : ℝ) - ε * X) < Real.goldenRatio := by
  have hn2nat : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hn2 : (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hn2nat
  have hXlt : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hX0 : (0 : ℝ) < X := by linarith
  have hεX : ε * X < 3 * (⌊X⌋₊ : ℝ) / 13 := by
    nlinarith [mul_le_mul_of_nonneg_right hε hX0.le, hXlt, hn2]
  have hden : (0 : ℝ) < (⌊X⌋₊ : ℝ) - ε * X := by nlinarith [hεX, hn2]
  rw [div_lt_iff₀ hden]
  nlinarith [hεX, goldenRatio_ge, mul_nonneg (sub_nonneg.mpr goldenRatio_ge) hden.le]
end SumProduct
