-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.vertex_table_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:30.888113+00:00
-- url     : https://prove2.me/submissions/03d893da-76aa-486b-9b64-4b6f20a6136d

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
    Tendsto (fun h : ℕ => Real.log ((512 * h).choose h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (ThreeSum.Parameters.E + 1 / 2 + ThreeSum.Parameters.kappa / 2)) := by
  have h := (fixed_ratio_bits_tendsto (c := 512) (r := 1) (by norm_num) (by norm_num)).div_const 2
  convert h using 1
  · funext m
    simp only [Nat.one_mul, div_div]
    congr 1
    ring
  · norm_num [ThreeSum.Parameters.E, ThreeSum.Parameters.kappa]
    ring
end ThreeSum.BinomialEntropy
