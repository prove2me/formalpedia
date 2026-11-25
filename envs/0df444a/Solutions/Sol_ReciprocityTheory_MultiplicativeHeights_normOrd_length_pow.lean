-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.normOrd_length_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:44.921264+00:00
-- url     : https://prove2.me/submissions/3aabc0f4-b029-4030-80fd-ff2e4d7fb4ec

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_NormOrdLengthResidue
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_normOrd_length_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (O B : Type) [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (P : Ideal B) [P.IsMaximal] (hP0 : P ≠ ⊥) (n : ℕ) :
    length O (B ⧸ P ^ n) = n * length O (B ⧸ P) := by
  induction n with
  | zero =>
    have : Subsingleton (B ⧸ P ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ n ih =>
    rw [normOrd_length_succ O B P hP0 n, ih]
    push_cast
    ring
end ReciprocityTheory.MultiplicativeHeights
