-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupportConcrete.flatten_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:41.55355+00:00
-- url     : https://prove2.me/submissions/5fda56d3-0081-40b4-96b1-9f51f033d650

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
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
open ThreeSum ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryPairedSupportConcrete
theorem _root_.solution (J : ℕ) : Function.Injective (flatten (K := K) J) := by
  intro u v h
  apply Prod.ext
  · funext j
    have hh := congrFun h (finSumFinEquiv (Sum.inl j))
    simpa [flatten] using hh
  · apply Prod.ext
    · have hh := congrFun h (finSumFinEquiv (Sum.inr (0 : Fin 2)))
      simpa [flatten] using hh
    · have hh := congrFun h (finSumFinEquiv (Sum.inr (1 : Fin 2)))
      simpa [flatten] using hh
end ThreeSum.TernaryPairedSupportConcrete
