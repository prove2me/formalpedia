-- Prove2me | solution 1 for ThreeSum.TernaryHybridCore.solves_of_fast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:14:30.993526+00:00
-- url     : https://prove2.me/submissions/a715c44b-9c82-4bc3-9e1f-f119bba45da6

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Theorems.Thm_ThreeSum_TernaryHybridCore_main_lookup
import Theorems.Thm_ThreeSum_TernaryHybridCore_program_meets_of_fast
import Theorems.Thm_Light_ArrayAt_mono
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_ListAt_mono
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_Light_TriInst_Pre_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_Light_getElem__append_of_eq_some_9fa037aa12b5
import Theorems.Thm_ThreeSumApsp_AbsLe_append
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
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_OriginalThreeSum_task_bound
import Theorems.Thm_ThreeSum_OriginalThreeSum_task_post
import Theorems.Thm_ThreeSum_OriginalThreeSum_task_read
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
theorem _root_.solution {fastP : Program} {fastProc κ cutoff : ℕ}
    (hfast : ∀ {lim : Limits} {src n free d : ℕ},
      ∀ (x : Fin n → ℤ) (μ : ℕ → ℤ),
        cutoff ≤ n → 0 < n → src+n ≤ free →
        (fastNeed n (n^κ)).Ok lim free d →
        Seg μ src (List.ofFn x) → (∀ i, |x i| ≤ ((n^κ : ℕ) : ℤ)) →
        Meets lim fastP fastProc d [src,n,free] μ (fastTime n)
          (fun r ν => (r=0 ∨ r=1) ∧
            (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free)) :
    Solves s3Task (program fastP fastProc κ cutoff) (fastP.length+5)
      (time fastTime κ cutoff) (TernaryHybridResources.need fastNeed κ cutoff) := by
  refine ⟨body fastP.length fastProc κ cutoff,
    main_lookup fastP fastProc κ cutoff, fun R lim d x μ free H hok => ?_⟩
  have hp := getElem?_append_of_eq_some (main_lookup fastP fastProc κ cutoff) R
  have hinput : Seg μ x.a (List.ofFn (ThreeSumApsp.Spec.vecOf x.N x.X)) := by
    intro i hi
    have hi' : i < x.N := by simpa only [List.length_ofFn] using hi
    simpa only [List.getElem_ofFn] using (OriginalThreeSum.task_read H) ⟨i,hi'⟩
  have hh := (program_meets_of_fast fastNeed fastTime
    (κ := κ) (cutoff := cutoff) (d := d) (ThreeSumApsp.Spec.vecOf x.N x.X) μ
    H.N_pos H.below hok hinput (OriginalThreeSum.task_bound H) hfast).append R
  obtain ⟨b,hb,he⟩ := hh.mono le_rfl (fun r ν ⟨hbool,hcorrect,hkept⟩ =>
    OriginalThreeSum.task_post (x := x) (μ := μ) (ν := ν) (fr := free)
      hbool hcorrect hkept)
  have heq : b=body fastP.length fastProc κ cutoff :=
    Option.some.inj (hb.symm.trans hp)
  subst b
  exact he
end ThreeSum.TernaryHybridCore
