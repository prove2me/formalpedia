-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.output_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:09:02.459933+00:00
-- url     : https://prove2.me/submissions/4b04f5d1-29d6-416d-955f-6f79d8f7fff2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_code
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_value
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_actual
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangle_labels
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_injective
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ)
    (r : ColorRow (BDL26NativeStateRows.Index S n)) (hr : r∈(colorsQ S n).value) :
    ∃!t : Triangle (P S n),nativeRow S n t=r := by
  rw [colors_value] at hr
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hr
  obtain ⟨t,ht⟩ := (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc
  refine ⟨t,?_,?_⟩
  · rw [←he,←ht]
    exact (row_actual S n t).symm
  · intro u hu
    apply BDL26NativeTriangleKeys.encode_injective S n
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.fst he
    change encode S n u=r.1 at h1
    rw [row_code] at h2
    exact h1.trans (h2.symm.trans ht.symm)
end QEC.Coding.BDL26NativeTriangleColors
