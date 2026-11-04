-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.entropy_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:25.27736+00:00
-- url     : https://prove2.me/submissions/bc5d927f-8fa0-4bb0-9106-bb887541e9a5

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
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) = (n : ℝ) * Real.log n -
      (k : ℝ) * Real.log k - ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by
  have hn : (n : ℝ) ≠ 0 := by have : 0 < n := lt_trans hk0 hk; positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  have hsub' : ((n - k : ℕ) : ℝ) ≠ 0 := by positivity
  have hcomp : (1 : ℝ) - (k : ℝ) / n = ((n - k : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hk.le]
    field_simp
  unfold Real.binEntropy
  simp only [Real.log_inv]
  rw [hcomp, Real.log_div hk' hn, Real.log_div hsub' hn]
  rw [Nat.cast_sub hk.le]
  field_simp
  ring
end ThreeSum.BinomialEntropy
