-- Prove2me | solution 1 for ThreeSum.WeightedGlobalRadixOverhead.polynomial_dimension_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:22:43.203257+00:00
-- url     : https://prove2.me/submissions/612f21f0-ceef-41b6-ae15-68409e84485c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalRadixOverhead_polynomial_radix_budget
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRadixOverhead
open Filter Real Asymptotics WeightedGlobalCoverScale WeightedGlobalPrincipalDimensions
open scoped Topology
namespace ThreeSum.WeightedGlobalRadixOverhead
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
end ThreeSum.WeightedGlobalRadixOverhead
