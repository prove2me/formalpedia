-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedPreparationBudget.binary_logarithmic_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:27.244833+00:00
-- url     : https://prove2.me/submissions/c444d886-471a-4002-bf51-a7b219a5a1de

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos

noncomputable section
namespace ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology
private theorem floor_log_linear_bound {b x : ℕ} (hb : 1<b) (hx : 0<x) :
    (Nat.log b x : ℝ)≤Real.log (x : ℝ)/Real.log (b : ℝ) := by
  have hbR : (1 : ℝ)<b := by exact_mod_cast hb
  have hbp : (0 : ℝ)<b := by linarith
  have hh : (b : ℝ)^(Nat.log b x)≤(x : ℝ) := by exact_mod_cast Nat.pow_log_le_self b hx.ne'
  have hl := Real.log_le_log (pow_pos hbp _) hh
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos hbR)).mpr hl
end ThreeSum.WeightedGlobalSignedPreparationBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology
namespace ThreeSum.WeightedGlobalSignedPreparationBudget
theorem _root_.solution {n U : ℕ} (hn : 1<n) {κ : ℝ} (hκ : 0≤κ)
    (hU : (U : ℝ)≤(n : ℝ)^κ) (hlog : 1≤Real.log (n : ℝ)) :
    (Nat.log 2 (3*U+1) : ℝ)+2≤binaryConstant κ*Real.log (n : ℝ) := by
  have hnR : (1 : ℝ)<n := by exact_mod_cast hn
  have hnp : (0 : ℝ)<n := by linarith
  have hp : (1 : ℝ)≤(n : ℝ)^κ := Real.one_le_rpow hnR.le hκ
  have hsize : ((3*U+1 : ℕ) : ℝ)≤4*(n : ℝ)^κ := by push_cast; linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<((3*U+1 : ℕ) : ℝ)) hsize
  rw [Real.log_mul (by norm_num : (4 : ℝ)≠0) (Real.rpow_pos_of_pos hnp κ).ne',Real.log_rpow hnp] at hl
  have hfour : Real.log 4=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hfour] at hl
  have hb := floor_log_linear_bound (by decide : 1<(2 : ℕ)) (by omega : 0<3*U+1)
  have hh := div_le_div_of_nonneg_right hl log_two_pos.le
  have he : (2*Real.log 2+κ*Real.log (n : ℝ))/Real.log 2=
      2+κ/Real.log 2*Real.log (n : ℝ) := by field_simp
  rw [he] at hh
  unfold binaryConstant
  nlinarith only [hb,hh,hlog]
end ThreeSum.WeightedGlobalSignedPreparationBudget
