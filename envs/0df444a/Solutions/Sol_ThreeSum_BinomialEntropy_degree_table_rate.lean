-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.degree_table_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:03.846294+00:00
-- url     : https://prove2.me/submissions/6ae4a544-743e-44a4-b8af-f99fbabf7dd3

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_bits_tendsto

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution :
    Tendsto (fun h : ℕ => Real.log ((511 * h).choose h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 ((511 / 2 : ℝ) * ThreeSum.Parameters.entropy (1 / 511))) := by
  have h := (fixed_ratio_bits_tendsto (c := 511) (r := 1) (by norm_num) (by norm_num)).div_const 2
  convert h using 1
  · funext m
    simp only [Nat.one_mul, div_div]
    congr 1
    ring
  · norm_num
    ring
end ThreeSum.BinomialEntropy
