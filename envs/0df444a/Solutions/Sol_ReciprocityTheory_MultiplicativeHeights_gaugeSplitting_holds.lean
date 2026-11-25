-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gaugeSplitting_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:18.512213+00:00
-- url     : https://prove2.me/submissions/2655f7b8-65ab-4a9c-94ea-e7234c8308b9

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Lemmata_GeneralBFactLast_Imports
import Definitions.Def_Lemmata_GeneralBFactTail_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetSubtypeCompAssociatedProd
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_det_subtype_comp_associated_prod
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_addVal_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module Submodule
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : NormLengthStatement := by
  intro O B _ _ _ _ _ _ _ _ g hg
  classical
  have : Module.Free O B := Module.free_iff_isTorsionFree.mpr inferInstance
  set b := Module.Free.chooseBasis O B
  set I : Ideal B := Ideal.span ({g} : Set B)
  have hI : I ≠ ⊥ := by simpa [I] using hg
  have h := Ideal.finrank_eq_finrank b I hI
  have hlen : Module.length O (B ⧸ I) =
      ∑ i, IsDiscreteValuationRing.addVal O (smithNormalFormCoeffs b h i) := by
    rw [(Ideal.quotientEquivPiSpan I b hI).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (Algebra.norm O g) (∏ i, smithNormalFormCoeffs b h i) := by
    rw [Algebra.norm_apply]
    have key := det_subtype_comp_associated_prod b (I.restrictScalars O) h
      (b.equiv (Ideal.basisSpanSingleton b hg) (Equiv.refl _))
    convert key using 2
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    have h1 := Basis.equiv_apply (b := b) (b' := Ideal.basisSpanSingleton b hg) (e := Equiv.refl _) i
    refine Eq.trans ?_ (congrArg Subtype.val h1).symm
    rw [Equiv.refl_apply, Ideal.basisSpanSingleton_apply]
    rfl
  rw [hlen, ← addVal_prod, ← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal]
  exact Ring.ord_eq_of_associated hdet
end ReciprocityTheory.MultiplicativeHeights
