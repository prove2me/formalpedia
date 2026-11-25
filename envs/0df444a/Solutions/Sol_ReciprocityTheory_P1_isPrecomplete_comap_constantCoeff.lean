-- Prove2me | solution 1 for ReciprocityTheory.P1.isPrecomplete_comap_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:19:10.383485+00:00
-- url     : https://prove2.me/submissions/392f416a-458d-4278-b83b-33cbddcafdcf

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
theorem _root_.solution [IsPrecomplete I A] :
    IsPrecomplete (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  prec' F hF := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_pow_comap_constantCoeff_iff] at hF ⊢
    have : ∀ i, ∃ L : A, ∀ n, coeff i (F (n + i)) - L ∈ I ^ n := by
      intro i
      have := IsPrecomplete.prec' (I := I) (fun n => coeff i (F (n + i))) (by
        intro m n h
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using hF (show m + i ≤ n + i by omega) i)
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using this
    choose L hL using this
    refine ⟨mk L, fun n i => ?_⟩
    rcases le_or_gt i n with h | h
    · have := hL i (n - i)
      rw [Nat.sub_add_cancel h] at this
      simpa using this
    · rw [show n - i = 0 by omega]; simp
end ReciprocityTheory.P1
