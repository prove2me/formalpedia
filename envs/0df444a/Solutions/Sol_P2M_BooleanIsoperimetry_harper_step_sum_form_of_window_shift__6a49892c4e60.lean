-- Prove2me | solution 1 for P2M_BooleanIsoperimetry_harper_step_sum_form_of_window_shift__6a49892c4e60
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:32.271795+00:00
-- url     : https://prove2.me/submissions/f2fe7f1f-61e4-4929-a6c8-4380f73fcdf4

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_eq_H_sub
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    {a b p q : ℕ}
    (hpa : p ≤ a) (hbq : b ≤ q)
    (hwin :
      gShiftIntervalCount (n + 1) b q ≤
        gShiftIntervalCount (n + 1) p a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  have hap := gShiftIntervalCount_eq_H_sub (n + 1) p a hpa
  have hqb' := gShiftIntervalCount_eq_H_sub (n + 1) b q hbq
  rw [hap, hqb'] at hwin
  have hHp : H (n + 1) p ≤ H (n + 1) a := H_mono hpa
  have hHb : H (n + 1) b ≤ H (n + 1) q := H_mono hbq
  omega
end BooleanIsoperimetry
