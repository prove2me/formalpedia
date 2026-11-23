-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.spanIdx_eq_vecIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:11.105364+00:00
-- url     : https://prove2.me/submissions/7a16c490-1c2f-4e33-b7fd-5b675f0eea78

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_injective
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_map_coordLat
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_combMap_intVec
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : spanIdx B b = vecIdx (coordLat B b) := by
  have hinj := combMap_injective hb.2.1
  have hspan : (intVec K k).map ((combMap b).restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range b) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨t, ht, rfl⟩
      exact combMap_intVec ht _ fun i => Submodule.subset_span ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, (Submodule.mem_pi).2 fun j _ => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Pi.single_apply, if_pos rfl]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
        · rw [Pi.single_apply, if_neg hj]; exact zero_mem _
      · show combMap b (Pi.single i 1) = b i
        simp [combMap_apply, Pi.single_apply, ite_smul]
  have e1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup =
      (intVec K k).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    rw [← hspan]; exact AddSubgroup.ext fun _ => Iff.rfl
  have e2 : B.toAddSubgroup =
      (coordLat B b).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    conv_lhs => rw [← map_coordLat hb]
    exact AddSubgroup.ext fun _ => Iff.rfl
  unfold spanIdx vecIdx
  rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
