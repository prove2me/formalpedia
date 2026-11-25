-- Prove2me | solution 1 for SCCThm8.sum_cntRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:57.167917+00:00
-- url     : https://prove2.me/submissions/ec785b4c-e4ae-47ba-9be8-defe7ba8e6c6

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} (f : ℕ → ℤ) (v : Finset (Fin n)) :
    ∑ i ∈ v, f (cntRank v i) = ∑ r ∈ range v.card, f r := by
  induction v using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [sum_insert has, card_insert_of_notMem has, sum_range_succ]
    have h1 : cntRank (insert a s) a = s.card := by
      unfold cntRank
      rw [filter_insert, if_neg (lt_irrefl a), filter_true_of_mem ha]
    have h2 : ∀ i ∈ s, cntRank (insert a s) i = cntRank s i := by
      intro i hi
      unfold cntRank
      rw [filter_insert, if_neg (not_lt.2 (ha i hi).le)]
    rw [h1, add_comm, ← ih]
    congr 1
    exact sum_congr rfl fun i hi => by rw [h2 i hi]
end SCCThm8
