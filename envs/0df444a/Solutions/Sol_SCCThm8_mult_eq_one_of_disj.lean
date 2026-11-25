-- Prove2me | solution 1 for SCCThm8.mult_eq_one_of_disj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:57.962777+00:00
-- url     : https://prove2.me/submissions/c1384393-e782-4712-8953-3e2b58466330

module
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution (k : ℕ) (A B C : Finset (Fin (3 * k)))
    (hA : A.card = k) (hB : B.card = k) (hC : C.card = k)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (i : Fin (3 * k)) :
    mult A B C i = 1 := by
  have hU : A ∪ B ∪ C = univ := by
    apply Finset.eq_univ_of_card
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hAC, hBC⟩),
      card_union_of_disjoint hAB, hA, hB, hC, Fintype.card_fin]
    ring
  have hi : i ∈ A ∪ B ∪ C := hU ▸ mem_univ i
  simp only [mem_union] at hi
  unfold mult
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;>
    simp_all [Finset.disjoint_left]
end SCCThm8
