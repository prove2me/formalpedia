-- Prove2me | solution 1 for ThreeSum.TernaryTypeLowerBound.block_count_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:54.801294+00:00
-- url     : https://prove2.me/submissions/8da7e71a-e4e2-4e50-bc45-55f7f4a78faa

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
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


noncomputable section
namespace ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal
private theorem indicator_one (P : Prop) [Decidable P] :
    (if (if P then (1 : Fin 3) else 0) = 1 then 1 else 0 : ℕ) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]
private theorem indicator_two_one (P : Prop) [Decidable P] :
    (if (if P then (2 : Fin 3) else 0) = 1 then 1 else 0 : ℕ) = 0 := by
  by_cases h : P <;> simp [h]
end ThreeSum.TernaryTypeLowerBound
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryTypeLowerBound
theorem _root_.solution {t1 t2 r : ℕ} (c : BlockChoice t1 t2) :
    count (blockWord (r := r) c) 1 = t1 := by
  simp only [count, Fintype.sum_sum_type, Fintype.sum_prod_type, blockWord]
  simp_rw [indicator_one, indicator_two_one]
  simp
end ThreeSum.TernaryTypeLowerBound
