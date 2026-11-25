-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.relIndex_cImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:50.998099+00:00
-- url     : https://prove2.me/submissions/098801c4-0911-4b6c-9cc0-eadd68e9fac2

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Definitions.Def_Lemmata_MiscLemmasR_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_one_map
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_cImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (hc : ∀ x, c (c x) = x) (C : Submodule (𝓞 K) K) :
    (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (cImage c C).toAddSubgroup =
      (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup := by
  have h1 : (1 : Submodule (𝓞 K) K).toAddSubgroup
      = (1 : Submodule (𝓞 K) K).toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    constructor
    · intro hx
      exact mem_one_map c hx
    · intro hx
      have h' : c (c x) ∈ (1 : Submodule (𝓞 K) K) := mem_one_map c hx
      rwa [hc] at h'
  have h2 : (cImage c C).toAddSubgroup = C.toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    exact mem_cImage c C
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  · rw [← h1]
  · exact fun y => ⟨c y, hc y⟩
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
