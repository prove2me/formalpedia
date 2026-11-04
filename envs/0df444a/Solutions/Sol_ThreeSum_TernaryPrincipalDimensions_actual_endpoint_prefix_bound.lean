-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.actual_endpoint_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:55.667441+00:00
-- url     : https://prove2.me/submissions/82b31e4d-ad93-4eeb-975d-09a99949835f

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_prefix_dimension_bound
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_endpoint_charge_eq
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
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_endpoint_count
import Theorems.Thm_ThreeSum_TernaryEntropyRates_typeCount_pos
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
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (endpointSize m : ℝ)^j ≤ (endpointSize m : ℝ)*(n : ℝ)^endpointCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hA : 0 < endpointSize m := by rw [actual_endpoint_count]; exact typeCount_pos (by decide) m
  have hAr : 0 < (endpointSize m : ℝ) := by exact_mod_cast hA
  have ha : 0 ≤ Real.log (endpointSize m : ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  have h := prefix_dimension_bound hM hn hj ha (pow_nonneg (Nat.cast_nonneg _) j)
    (by rw [Real.log_pow] : Real.log ((endpointSize m : ℝ)^j) ≤ (j : ℝ)*Real.log (endpointSize m : ℝ))
  simpa only [Real.exp_log hAr,endpoint_charge_eq hm] using h
end ThreeSum.TernaryPrincipalDimensions
