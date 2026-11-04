-- Prove2me | solution 1 for ThreeSum.TernaryRadixOverhead.polynomial_dimension_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:45.753272+00:00
-- url     : https://prove2.me/submissions/3a5c7dbe-a4b8-4f80-9418-e4ddb848145b

import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Theorems.Thm_ThreeSum_TernaryRadixOverhead_polynomial_radix_budget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryRadixOverhead
open Filter Real Asymptotics TernaryCoverScale TernaryPrincipalDimensions
open scoped Topology
namespace ThreeSum.TernaryRadixOverhead
theorem _root_.solution {m : ℕ} (hm : 0 < m) (A K e q : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (he : e < q) (d : ℕ) (X : ℕ → ℝ)
    (hX : ∀ n : ℕ, 1 < n → X n ≤ K*(n : ℝ)^e) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d*X n ≤ (n : ℝ)^q := by
  have hb := polynomial_radix_budget hm (A*K) (mul_nonneg hA hK) d (sub_pos.mpr he)
  filter_upwards [hb,eventually_gt_atTop (1 : ℕ)] with n hb hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hp : 0 ≤ A*((radixLength m n : ℝ)+1)^d := by positivity
  calc
    _ ≤ A*((radixLength m n : ℝ)+1)^d*(K*(n : ℝ)^e) := mul_le_mul_of_nonneg_left (hX n hn) hp
    _ = ((A*K)*((radixLength m n : ℝ)+1)^d)*(n : ℝ)^e := by ring
    _ ≤ (n : ℝ)^(q-e)*(n : ℝ)^e := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hnp.le _)
    _ = _ := by rw [← Real.rpow_add hnp]; congr 1; ring
end ThreeSum.TernaryRadixOverhead
