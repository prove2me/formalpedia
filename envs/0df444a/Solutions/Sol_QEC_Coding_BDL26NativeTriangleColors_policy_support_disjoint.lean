-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.policy_support_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:10:20.374131+00:00
-- url     : https://prove2.me/submissions/9efd2b9c-ab82-442c-9d00-a6c3ccdba68b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_policy_same_vertex
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
variable (P : TannerSquarePresentation) (key : Triangle P → ℕ)
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (hk : Function.Injective key) {a b : Triangle P}
    (hne : a≠b) (hc : policyColor P key a=policyColor P key b) :
    Disjoint (triangleSupport P a) (triangleSupport P b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v ha hb
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hb
  exact hne (policy_same_vertex P key hk hc (hi.trans hj.symm))
end QEC.Coding.BDL26NativeTriangleColors
