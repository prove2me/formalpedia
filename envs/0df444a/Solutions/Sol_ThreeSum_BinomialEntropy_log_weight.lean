-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.log_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:24.129202+00:00
-- url     : https://prove2.me/submissions/ac571ccb-2133-4ec8-bf1c-090b1a217f9d

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    Real.log (weight n k k) = Real.log (n.choose k : ℝ) +
      (k : ℝ) * Real.log k + ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by
  have hc : 0 < n.choose k := Nat.choose_pos hk.le
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  unfold weight
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
end ThreeSum.BinomialEntropy
