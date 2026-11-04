-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.actual_bank_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:54.440206+00:00
-- url     : https://prove2.me/submissions/ddc59903-7ef6-4d5a-8e70-00328ff32b3b

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_prefix_dimension_bound
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_bank_charge_eq
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
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_bank_log_bound
import Theorems.Thm_ThreeSum_TernaryEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_TernaryParameters_analytic_admissibility
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
    (bankSize m j : ℝ) ≤ Real.exp ((fixedLength m : ℝ)*Real.log 2*bankEntropy)*
      (n : ℝ)^bankCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have ha : 0 ≤ (fixedLength m : ℝ)*Real.log 2*bankEntropy := by
    exact mul_nonneg (denominator_pos hm).le analytic_admissibility.1.le
  have hlog := bank_log_bound m j
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*bankEntropy) := by unfold fixedLength; push_cast; ring
  rw [he] at hlog
  simpa only [bank_charge_eq hm] using prefix_dimension_bound hM hn hj ha (Nat.cast_nonneg _) hlog
end ThreeSum.TernaryPrincipalDimensions
