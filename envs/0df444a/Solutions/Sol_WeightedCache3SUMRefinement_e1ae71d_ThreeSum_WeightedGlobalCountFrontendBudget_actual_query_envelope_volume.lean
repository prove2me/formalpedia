-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget.actual_query_envelope_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:40:51.385319+00:00
-- url     : https://prove2.me/submissions/669edbfd-8f80-4e74-95ec-e582fc9f3cef

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeDimensions_query_charge_eq
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeDimensions_query_slope_nonneg
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_gibbs_parameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_dimension_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_query_charge_eq


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
theorem _root_.solution {K m n j : ℕ} (hK : 0<K) (hm : 0<m) (hn : 1<n)
    (hj : j≤radixLength m n) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*envelope m j≤
      (Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^2739)*(n : ℝ)^WeightedGlobalOversizeRates.queryCharge K m := by
  have hM : 1<outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hp : 0<(nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hR : 0<(partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0<(inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hnR : 0<(n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hz := gibbs_parameters.2.2.1
  have hratio := div_pos hp hR
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*queryEntropy) := by unfold fixedLength; push_cast; ring
  have hX : 0≤((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy) := by positivity
  have hlog : Real.log (((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy))≤
      (j : ℝ)*WeightedGlobalOversizeDimensions.querySlope K m := by
    rw [Real.log_mul (mul_pos (pow_pos hratio _) (pow_pos hS _)).ne' (Real.exp_pos _).ne',
      Real.log_mul (pow_pos hratio _).ne' (pow_pos hS _).ne',Real.log_pow,Real.log_pow,
      Real.log_exp,Real.log_div hp.ne' hR.ne',he]
    unfold WeightedGlobalOversizeDimensions.querySlope
    push_cast
    nlinarith
  have hb := prefix_dimension_bound hM hn hj (query_slope_nonneg hK hm) hX hlog
  calc
    _=((n : ℝ)/z^2739)*(((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy)) := by unfold envelope; ring
    _≤((n : ℝ)/z^2739)*(Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)*
      (n : ℝ)^(2*WeightedGlobalOversizeDimensions.querySlope K m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_pos hnR (pow_pos hz 2739)).le
    _=_ := by rw [←WeightedGlobalOversizeDimensions.query_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCountFrontendBudget
