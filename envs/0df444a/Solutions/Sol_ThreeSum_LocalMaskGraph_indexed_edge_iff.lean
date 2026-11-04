-- Prove2me | solution 1 for ThreeSum.LocalMaskGraph.indexed_edge_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:29.815447+00:00
-- url     : https://prove2.me/submissions/9011b4c2-b363-4e60-b762-8c5ccd956d99

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_card
import Theorems.Thm_ThreeSum_LocalMaskGraph_indexed_dot_zero_iff
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
namespace ThreeSum.LocalMaskGraph
theorem _root_.solution {L h i j : ℕ}
    (hi : i < vertexCount L h) (hj : j < vertexCount L h) :
    LightBooleanDot.dot (LightMaskBits.bit L (maskAt L h i))
      (LightMaskBits.bit L (maskAt L h j)) L = 0 ↔
      (setAt L h i,setAt L h j) ∈ LayerCounts.edgeSet L h := by
  rw [LayerCounts.mem_edgeSet,indexed_dot_zero_iff hi hj]
  simp only [setAt_card hi,setAt_card hj,true_and]
end ThreeSum.LocalMaskGraph
