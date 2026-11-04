-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.weight_step_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:41:12.38903+00:00
-- url     : https://prove2.me/submissions/9300ed4c-a5c2-42e9-a40f-33355f341d15

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
theorem _root_.solution {n k j : ℕ} (hk : k < n) (hj : j < k) :
    weight n k j ≤ weight n k (j + 1) := by
  have hrec := weight_recurrence (k := k) (lt_trans hj hk)
  have hsub : 0 < n - k := Nat.sub_pos_of_lt hk
  have hcpos : 0 < ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by positivity
  have hfactor : ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) ≤
      ((n - j : ℕ) : ℝ) * (k : ℝ) := by
    rw [Nat.cast_sub hk.le, Nat.cast_sub (lt_trans hj hk).le, Nat.cast_add, Nat.cast_one]
    have hkj : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hkj)]
  have hmul := mul_le_mul_of_nonneg_left hfactor (weight_nonneg n k j)
  apply (mul_le_mul_iff_of_pos_right hcpos).mp
  nlinarith
end ThreeSum.BinomialEntropy
