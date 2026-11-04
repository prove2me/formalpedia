-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.actual_prime_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:56.836823+00:00
-- url     : https://prove2.me/submissions/3ec650e0-55dd-47dc-a632-836aa5618ff2

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_TernaryEntropyRates_prime_rate_bounds
import Theorems.Thm_ThreeSum_TernaryEntropyRates_prime_rate_error_tendsto
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
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
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
theorem _root_.solution :
    Tendsto primeRate atTop (𝓝 ((TernaryParameters.Hpi+TernaryParameters.partitionEntropy)/2)) := by
  have hl := (actual_output_rate.add_const TernaryParameters.partitionEntropy).div_const 2
  have hu := hl.add prime_rate_error_tendsto
  have hb : ∀ᶠ m : ℕ in atTop,
      (outputRate m+TernaryParameters.partitionEntropy)/2 ≤ primeRate m ∧
      primeRate m ≤ (outputRate m+TernaryParameters.partitionEntropy)/2+
        Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact prime_rate_bounds hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl (by simpa using hu)
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
end ThreeSum.TernaryEntropyRates
