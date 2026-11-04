-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.weight_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:26.932833+00:00
-- url     : https://prove2.me/submissions/e9e14255-b99e-4c8f-82f2-f483843ff71a

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
theorem _root_.solution {n k j : ℕ} (hj : j < n) :
    weight n k (j + 1) * ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) =
      weight n k j * ((n - j : ℕ) : ℝ) * (k : ℝ) := by
  have hc : (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hp : ((n - k : ℕ) : ℝ) ^ (n - j) =
      ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * ((n - k : ℕ) : ℝ) := by
    rw [show n - j = n - (j + 1) + 1 by omega, pow_succ]
  unfold weight
  rw [pow_succ, hp]
  calc
    _ = ((n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * k * (n - k : ℕ) := by ring
    _ = ((n.choose j : ℝ) * ((n - j : ℕ) : ℝ)) *
        (k : ℝ) ^ j * ((n - k : ℕ) : ℝ) ^ (n - (j + 1)) * k * (n - k : ℕ) := by rw [hc]
    _ = _ := by ring
end ThreeSum.BinomialEntropy
