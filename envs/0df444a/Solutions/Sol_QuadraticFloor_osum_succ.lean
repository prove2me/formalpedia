-- Prove2me | solution 1 for QuadraticFloor.osum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:21.492781+00:00
-- url     : https://prove2.me/submissions/ca0bdc29-d6a8-488c-91f3-d8632b827fb8

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_sum_Ico_eq_add_sum
public import Theorems.Thm_QuadraticFloor_ite_of_neg
public import Theorems.Thm_QuadraticFloor_ite_of_pos


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (t : ℤ) (g : ℤ → ℤ) : osum (t + 1) g = osum t g + g t := by
  unfold osum
  rcases lt_trichotomy t (-1) with h | h | h
  · rw [ite_of_neg (by omega), ite_of_neg (by omega), sum_Ico_eq_add_sum g (show t < 0 by omega)]
    ring
  · subst h
    have : Ico (-1 : ℤ) 0 = {-1} := by ext j; simp only [mem_Ico, mem_singleton]; omega
    simp [this]
  · rw [ite_of_pos (by omega), ite_of_pos (by omega), ← sum_Ico_add_eq_sum_Ico_add_one (by omega) g]
end QuadraticFloor
