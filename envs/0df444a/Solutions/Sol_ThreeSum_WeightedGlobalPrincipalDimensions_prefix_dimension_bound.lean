-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.prefix_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:35.115533+00:00
-- url     : https://prove2.me/submissions/01a1923b-be86-43da-b4a7-c1035c5e36bc

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_linear_bound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {M n j : ℕ} (hM : 1 < M) (hn : 1 < n)
    (hj : j ≤ Nat.clog M (n^2)) {a X : ℝ} (ha : 0 ≤ a) (hX : 0 ≤ X)
    (hlog : Real.log X ≤ (j : ℝ)*a) :
    X ≤ Real.exp a*(n : ℝ)^(2*a/Real.log M) := by
  rcases hX.eq_or_lt with hX | hX
  · rw [← hX]
    positivity
  have hl := hlog.trans (prefix_linear_bound hM hn hj ha)
  calc
    X=Real.exp (Real.log X) := (Real.exp_log hX).symm
    _ ≤ Real.exp (a+(2*a/Real.log M)*Real.log n) := Real.exp_le_exp.mpr hl
    _ = _ := by
      rw [Real.exp_add,Real.rpow_def_of_pos (by exact_mod_cast lt_trans Nat.zero_lt_one hn)]
      congr 2
      ring
end ThreeSum.WeightedGlobalPrincipalDimensions
