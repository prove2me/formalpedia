-- Prove2me | solution 1 for ThreeSum.TernaryHybridCore.program_meets_of_fast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:43.603765+00:00
-- url     : https://prove2.me/submissions/6f3fc9d4-b2d3-42bd-8442-bca760d6abc8

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Theorems.Thm_ThreeSum_TernaryHybridCore_program_meets
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
import Theorems.Thm_ThreeSumApsp_Spec_length_subMat
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
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Theorems.Thm_ThreeSum_LightClassFilter_program_meets
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Theorems.Thm_ThreeSum_LightColorParameters_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_TernaryHybridResources_fast_of_ok
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
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.Switch.mem_candidates
attribute [local simp] ThreeSumApsp.Spec.length_affL
attribute [local simp] ThreeSumApsp.Spec.length_subMat



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
variable (fastNeed : ℕ → ℕ → Need) (fastTime : ℕ → ℕ)
namespace ThreeSum.TernaryHybridCore
theorem _root_.solution {lim : Limits} {fastP : Program}
    {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n → ℤ) (μ : ℕ → ℤ) (hn : 0 < n) (hsrc : src+n ≤ free)
    (H : (TernaryHybridResources.need fastNeed κ cutoff n U).Ok lim free d)
    (hinput : Seg μ src (List.ofFn x)) (hx : ∀ i, |x i| ≤ (U : ℤ))
    (hfast : ∀ {lim : Limits} {src n free d : ℕ},
      ∀ (x : Fin n → ℤ) (μ : ℕ → ℤ),
        cutoff ≤ n → 0 < n → src+n ≤ free →
        (fastNeed n (n^κ)).Ok lim free d →
        Seg μ src (List.ofFn x) → (∀ i, |x i| ≤ ((n^κ : ℕ) : ℤ)) →
        Meets lim fastP fastProc d [src,n,free] μ (fastTime n)
          (fun r ν => (r=0 ∨ r=1) ∧
            (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+5) d
      [n,U,src,free] μ (time fastTime κ cutoff n U)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have hread : ∀ i : Fin n, μ (src+i.val)=x i := by
    intro i
    have hi : i.val < (List.ofFn x).length := by
      simpa only [List.length_ofFn] using i.isLt
    simpa only [List.getElem_ofFn] using hinput i.val hi
  apply program_meets fastNeed fastTime x μ hn hsrc H hread hx
  intro hcutoff hU
  apply hfast x μ hcutoff hn hsrc
    (TernaryHybridResources.fast_of_ok fastNeed H) hinput
  intro i
  exact (hx i).trans (Int.ofNat_le.mpr hU)
end ThreeSum.TernaryHybridCore
