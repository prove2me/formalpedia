-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.fixed_ratio_bits_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:07.914062+00:00
-- url     : https://prove2.me/submissions/96d72add-7450-4e5f-9128-18175999662e

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_tendsto

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 ((c : ℝ) * ThreeSum.Parameters.entropy ((r : ℝ) / c))) := by
  have h := (fixed_ratio_tendsto hc hr).div_const (Real.log 2)
  simpa [div_div, ThreeSum.Parameters.entropy, mul_div_assoc] using h
end ThreeSum.BinomialEntropy
