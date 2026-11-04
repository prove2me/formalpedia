-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.weight_step_down
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:41:13.563881+00:00
-- url     : https://prove2.me/submissions/1dfe6685-afcb-4b32-a4e9-d6892965ae14

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_nonneg
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_recurrence

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {n k j : ℕ} (hk : k < n) (hj : k ≤ j) :
    weight n k (j + 1) ≤ weight n k j := by
  by_cases hjn : j < n
  · have hrec := weight_recurrence (k := k) hjn
    have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
    have hcpos : 0 < ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by positivity
    have hfactor : ((n - j : ℕ) : ℝ) * (k : ℝ) ≤
        ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk.le, Nat.cast_sub hjn.le, Nat.cast_add, Nat.cast_one]
      have hkj : (k : ℝ) ≤ j := by exact_mod_cast hj
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.le
      have hn : 0 ≤ (n : ℝ) := by positivity
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hkj)]
    have hmul := mul_le_mul_of_nonneg_left hfactor (weight_nonneg n k j)
    apply (mul_le_mul_iff_of_pos_right hcpos).mp
    nlinarith
  · have hz : weight n k (j + 1) = 0 := by
      simp [weight, Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]
    rw [hz]
    exact weight_nonneg n k j
end ThreeSum.BinomialEntropy
