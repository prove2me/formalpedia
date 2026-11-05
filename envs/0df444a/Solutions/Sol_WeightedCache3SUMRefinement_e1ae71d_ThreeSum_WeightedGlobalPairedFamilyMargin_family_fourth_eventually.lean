-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin.family_fourth_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:41:22.086293+00:00
-- url     : https://prove2.me/submissions/5b75456e-b5d8-4772-971e-54c835258d15

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedFamilyMargin_baseRate_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedFamilyMargin_family_log_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_native_family_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_inflation_rate_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin
open Filter Real WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin
theorem _root_.solution {K : ℕ} (hK : 16<K) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, (9*(nativeFamily K m k).length)^4≤outputSize m := by
  have hk : 0<K := by omega
  have hlim := ((baseRate_tendsto.add ((inflation_rate_tendsto hk).const_mul 4)).const_mul 4).sub actual_output_rate
  have hneg : 4*(0+4*(Hpi/(K : ℝ)))-Hpi<0 := by
    have hkr : (16 : ℝ)<K := by exact_mod_cast hK
    have hkp : (0 : ℝ)<K := by positivity
    apply (sub_neg).mpr
    field_simp [hkp.ne']
    nlinarith [Hpi_pos]
  have hsmall := hlim.eventually (gt_mem_nhds hneg)
  filter_upwards [hsmall,eventually_gt_atTop (0 : ℕ)] with m hsmall hm
  have hb := family_log_bound hk hm k
  have hd := denominator_pos hm
  have hout := outputSize_pos m
  have hf : 0<(nativeFamily K m k).length := by
    rw [native_family_length]
    exact Nat.mul_pos (Nat.mul_pos (by have := WeightedGlobalCoverCapParameters.frequencyFactor_gt_one m; omega)
      (pow_pos (inflation_pos hk m) 4)) (Nat.succ_pos _)
  have hlog : 4*Real.log (9*(nativeFamily K m k).length : ℝ)≤Real.log (outputSize m : ℝ) := by
    unfold outputRate at hsmall
    have hh : 4*(Real.log (9*(nativeFamily K m k).length : ℝ)/((fixedLength m : ℝ)*Real.log 2)) <
        Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2) := by linarith
    have hh' := (div_lt_div_iff_of_pos_right hd).mp (show
      (4*Real.log (9*(nativeFamily K m k).length : ℝ))/((fixedLength m : ℝ)*Real.log 2)<
        Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2) by convert hh using 1 <;> ring)
    exact hh'.le
  have hr : (9*(nativeFamily K m k).length : ℝ)^4≤(outputSize m : ℝ) := by
    apply (Real.log_le_log_iff (by positivity) (by exact_mod_cast hout)).mp
    rw [Real.log_pow]
    norm_num
    exact hlog
  exact_mod_cast hr
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedFamilyMargin
