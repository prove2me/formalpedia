-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupportConcrete.cast_tupleMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:52.110426+00:00
-- url     : https://prove2.me/submissions/70cfe3f7-3ae5-46fe-b83c-b705eb7c3210

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_cast_flattenInt
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
variable {P W D : Type*} [Fintype P] [Fintype K]
  [AddCommGroup W] [Module K W] [Fintype W] [DecidableEq D]
namespace ThreeSum.TernaryPairedSupportConcrete
theorem _root_.solution {J m : ℕ} (L R : P → Fin J → ℤ) (e : Fin m → P) :
    (fun i j => (tupleMatrix L R e i j : K)) =
      fun i => flatten J (taggedEndpoints (K := K)
        (fun i j => (L (e i) j : K)) (fun i j => (R (e i) j : K)) i) := by
  funext i
  cases i with
  | inl i => simpa [tupleMatrix,taggedEndpoints] using cast_flattenInt (K := K) J (L (e i),(1,0))
  | inr i => simpa [tupleMatrix,taggedEndpoints] using cast_flattenInt (K := K) J (R (e i),(0,1))
end ThreeSum.TernaryPairedSupportConcrete
