-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.cImage_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:58.392836+00:00
-- url     : https://prove2.me/submissions/ca733b67-6afd-4ebe-9d04-8f92a7709d86

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Definitions.Def_Lemmata_MiscLemmasR_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_intInv_coe
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (C : Submodule (𝓞 K) K) (hC : C.FG) : (cImage c C).FG := by
  haveI : RingHomSurjective (intInv c) :=
    ⟨fun y => ⟨intInv c y, by
      apply RingOfIntegers.ext
      show algebraMap (𝓞 K) K (intInv c (intInv c y)) = algebraMap (𝓞 K) K y
      rw [intInv_coe, intInv_coe, hc]⟩⟩
  let f : K →ₛₗ[intInv c] K :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, intInv_coe] }
  have h : cImage c C = C.map f := by
    ext x
    rw [mem_cImage, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨c x, hx, hc x⟩
    · rintro ⟨y, hy, rfl⟩
      show c (c y) ∈ C
      rw [hc]
      exact hy
  rw [h]
  exact hC.map f
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
