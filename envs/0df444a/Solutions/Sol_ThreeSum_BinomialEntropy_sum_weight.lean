-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.sum_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:21.767718+00:00
-- url     : https://prove2.me/submissions/6cd89e5a-94be-4a00-9bfe-d150b85b6b6d

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
theorem _root_.solution {n k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ range (n + 1), weight n k j = (n : ℝ) ^ n := by
  have h := add_pow (k : ℝ) ((n - k : ℕ) : ℝ) n
  rw [← Nat.cast_add, Nat.add_sub_of_le hk] at h
  rw [h]
  apply sum_congr rfl
  intro j _
  unfold weight
  ring
end ThreeSum.BinomialEntropy
