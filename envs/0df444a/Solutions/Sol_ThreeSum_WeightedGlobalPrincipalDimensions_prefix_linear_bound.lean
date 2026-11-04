-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.prefix_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:04:39.724309+00:00
-- url     : https://prove2.me/submissions/e08c46d5-001d-4e06-9184-9f2095e75fa2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_clog_power_upper

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {M n j : ℕ} (hM : 1 < M) (hn : 1 < n)
    (hj : j ≤ Nat.clog M (n^2)) {a : ℝ} (ha : 0 ≤ a) :
    (j : ℝ)*a ≤ a+(2*a/Real.log M)*Real.log n := by
  have hMr : (1 : ℝ) < M := by exact_mod_cast hM
  have hnr : (1 : ℝ) < n := by exact_mod_cast hn
  have hLM := Real.log_pos hMr
  have hMp : 0 < (M : ℝ) := by linarith
  have hnp : 0 < (n : ℝ) := by linarith
  have hp : (M : ℝ)^(Nat.clog M (n^2)) ≤ (M : ℝ)*(n : ℝ)^2 := by
    exact_mod_cast clog_power_upper hM hn
  have hl := Real.log_le_log (pow_pos hMp _) hp
  rw [Real.log_pow,Real.log_mul hMp.ne' (pow_pos hnp _).ne',Real.log_pow] at hl
  norm_num at hl
  have hji : (j : ℝ) ≤ Nat.clog M (n^2) := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_right hji hLM.le
  have hb := mul_le_mul_of_nonneg_right (hh.trans hl) ha
  have he : a+(2*a/Real.log M)*Real.log n=
      (a*Real.log M+2*a*Real.log n)/Real.log M := by field_simp
  rw [he]
  apply (le_div_iff₀ hLM).mpr
  nlinarith
end ThreeSum.WeightedGlobalPrincipalDimensions
