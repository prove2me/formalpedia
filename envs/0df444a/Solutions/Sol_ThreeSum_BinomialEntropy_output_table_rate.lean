-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.output_table_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:25.0225+00:00
-- url     : https://prove2.me/submissions/eda29e8d-e9d6-4945-9a93-efdfde25136d

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
    Tendsto (fun m : ℕ => Real.log ((256 * m).choose m : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 (2 * ThreeSum.Parameters.E)) := by
  have h := fixed_ratio_bits_tendsto (c := 256) (r := 1) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [ThreeSum.Parameters.E] <;> ring
end ThreeSum.BinomialEntropy
