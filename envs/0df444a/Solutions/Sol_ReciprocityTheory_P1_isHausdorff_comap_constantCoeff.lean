-- Prove2me | solution 1 for ReciprocityTheory.P1.isHausdorff_comap_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:51.489617+00:00
-- url     : https://prove2.me/submissions/5b57d9ae-57fb-4ad0-bd70-8d781e36113a

import Mathlib
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_ReciprocityTheory_P1_mem_pow_comap_constantCoeff_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PowerSeries IsLocalRing
noncomputable section
open ReciprocityTheory ReciprocityTheory.P1
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace ReciprocityTheory.P1
theorem _root_.solution [IsHausdorff I A] :
    IsHausdorff (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  haus' f hf := by
    ext i
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hf (n + i)
    rw [SModEq.zero] at this ⊢
    simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
    simpa using (mem_pow_comap_constantCoeff_iff I _ f).1 this i
end ReciprocityTheory.P1
