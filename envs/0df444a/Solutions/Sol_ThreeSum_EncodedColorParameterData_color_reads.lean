-- Prove2me | solution 1 for ThreeSum.EncodedColorParameterData.color_reads
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:45.085998+00:00
-- url     : https://prove2.me/submissions/faefa6aa-140f-428d-8933-809450abb573

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero



set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorParameterData
open Light Scales BandScales
namespace ThreeSum.EncodedColorParameterData
theorem _root_.solution {μ : ℕ → ℤ} {row W : ℕ} {color : Coloring.Parameter W}
    (H : Seg μ row (ColorParameters.fields color)) :
    μ row=(color.1.1.val : ℤ) ∧ μ (row+1)=(color.1.2.val : ℤ) ∧
    μ (row+2)=((color.2 (false,false)).val : ℤ) ∧ μ (row+3)=((color.2 (false,true)).val : ℤ) ∧
    μ (row+4)=((color.2 (true,false)).val : ℤ) ∧ μ (row+5)=((color.2 (true,true)).val : ℤ) := by
  have h (i : ℕ) (hi : i < 6) := H.getD (i := i) (by simpa [ColorParameters.fields] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [ColorParameters.fields] using h 0 (by omega)
  · simpa [ColorParameters.fields] using h 1 (by omega)
  · simpa [ColorParameters.fields] using h 2 (by omega)
  · simpa [ColorParameters.fields] using h 3 (by omega)
  · simpa [ColorParameters.fields] using h 4 (by omega)
  · simpa [ColorParameters.fields] using h 5 (by omega)
end ThreeSum.EncodedColorParameterData
