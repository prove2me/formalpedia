-- Prove2me | solution 1 for ThreeSum.TernaryRadixOverhead.polynomial_radix_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:30.123074+00:00
-- url     : https://prove2.me/submissions/2f9199d7-f173-40c7-bddc-30d409ba056c

import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_output_log_pos
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_prefix_linear_bound
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryRadixOverhead
open Filter Real Asymptotics TernaryCoverScale TernaryPrincipalDimensions
open scoped Topology
namespace ThreeSum.TernaryRadixOverhead
theorem _root_.solution {m : ℕ} (hm : 0 < m) (A : ℝ) (hA : 0 ≤ A)
    (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d ≤ (n : ℝ)^ε := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hLM := output_log_pos hm
  let c : ℝ := 2+2/Real.log (outputSize m : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hpow := (isLittleO_log_rpow_rpow_atTop (d : ℝ) hε).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hb := (hpow.const_mul_left (A*c^d)).bound (by norm_num : (0 : ℝ) < 1)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hb,hlog,eventually_gt_atTop (1 : ℕ)] with n hb hnlog hn
  dsimp only [Function.comp_apply] at hb hnlog
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hr := prefix_linear_bound hM hn (le_rfl : Nat.clog (outputSize m) (n^2) ≤ _) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at hr
  have hrb : (radixLength m n : ℝ)+1 ≤ c*Real.log n := by
    unfold radixLength at *
    dsimp [c]
    nlinarith
  have hrp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (radixLength m n : ℝ)+1) hrb d
  have ha := mul_le_mul_of_nonneg_left hrp hA
  have hcLog : 0 ≤ A*c^d*(Real.log (n : ℝ))^d := by positivity
  have hnrpow : 0 ≤ (n : ℝ)^ε := by positivity
  rw [Real.rpow_natCast] at hb
  have hbb : A*c^d*(Real.log (n : ℝ))^d ≤ (n : ℝ)^ε := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hcLog,abs_of_nonneg hnrpow,one_mul] using hb
  have haa : A*((radixLength m n : ℝ)+1)^d ≤ A*c^d*(Real.log (n : ℝ))^d := by
    simpa only [mul_pow,← mul_assoc] using ha
  exact haa.trans hbb
end ThreeSum.TernaryRadixOverhead
