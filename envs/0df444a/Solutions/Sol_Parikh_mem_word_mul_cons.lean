-- Prove2me | solution 1 for Parikh.mem_word_mul_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:05.315695+00:00
-- url     : https://prove2.me/submissions/604c39b6-0876-4151-8961-67e013f71733

module
public import Mathlib.Computability.DFA
public import Mathlib.Computability.NFA
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (a b : T) (u x : List T) (L : Language T) :
    a :: x ∈ ({b :: u} : Language T) * L ↔
      a = b ∧ x ∈ ({u} : Language T) * L := by
  simp only [Language.mem_mul]
  change (∃ p, p = b :: u ∧ ∃ v ∈ L, p ++ v = a :: x) ↔
    a = b ∧ ∃ p, p = u ∧ ∃ v ∈ L, p ++ v = x
  simp only [exists_eq_left, List.cons_append, List.cons.injEq]
  constructor
  · rintro ⟨v, hv, hab, hx⟩
    exact ⟨hab.symm, v, hv, hx⟩
  · rintro ⟨hab, v, hv, hx⟩
    exact ⟨v, hv, hab.symm, hx⟩
end Parikh
