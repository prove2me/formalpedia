-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.incidence_dimension_expression_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:22:28.570214+00:00
-- url     : https://prove2.me/submissions/e30ef574-469b-4a5d-83c6-1081ae0894a7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_dimension_bound
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_incidence_slope_pos
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_incidence_charge_eq
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j ≤
      Real.exp (incidenceSlope m)*(n : ℝ)^incidenceCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hMr : 0 < (outputSize m : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hM
  have hpr : 0 < (prime m : ℝ) := by exact_mod_cast (prime_prime m).pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hratio := div_pos hMr hpr
  have hlog : Real.log (((outputSize m : ℝ)/prime m)^j) ≤ (j : ℝ)*incidenceSlope m := by
    rw [Real.log_pow,Real.log_div hMr.ne' hpr.ne']
    rfl
  have hb := prefix_dimension_bound hM hn hj (incidence_slope_pos hm hs).le (pow_pos hratio _).le hlog
  calc
    _ ≤ (n : ℝ)*(Real.exp (incidenceSlope m)*(n : ℝ)^(2*incidenceSlope m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb hnR.le
    _ = _ := by rw [← incidence_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring
end ThreeSum.WeightedGlobalPrincipalDimensions
