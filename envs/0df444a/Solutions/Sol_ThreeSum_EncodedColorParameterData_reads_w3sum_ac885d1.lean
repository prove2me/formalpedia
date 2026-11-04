-- Prove2me | solution 1 for ThreeSum.EncodedColorParameterData.reads_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:25.859576+00:00
-- url     : https://prove2.me/submissions/f9067897-ba59-4858-bc63-98ff9106cbe6

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
import Theorems.Thm_ThreeSum_LightGlobalSizes_values_scales
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
theorem _root_.solution {μ : ℕ → ℤ} {params n : ℕ} (H : Seg μ params (LightParameterInit.values n)) :
    μ params=(inputBits n : ℤ) ∧ μ (params+1)=(microHalf (inputBits n) : ℤ) ∧
    μ (params+3)=(blockCount (inputBits n) : ℤ) ∧ μ (params+4)=(mu n : ℤ) ∧
    μ (params+14)=(radix n : ℤ) ∧ μ (params+17)=(bandSize n : ℤ) ∧
    μ (params+18)=(primeWindow n : ℤ) := by
  have h (i : ℕ) (hi : i < 19) := H.getD (i := i)
    (by simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,
      LightLocalCounts.values,LightGlobalSizes.values] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [LightParameterInit.values,LightScales.values] using h 0 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 1 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 3 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 4 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 14 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 17 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 18 (by omega)
end ThreeSum.EncodedColorParameterData
