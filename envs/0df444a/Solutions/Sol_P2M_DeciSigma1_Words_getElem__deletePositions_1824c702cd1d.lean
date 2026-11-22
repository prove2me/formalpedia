-- Prove2me | solution 1 for P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:19.939599+00:00
-- url     : https://prove2.me/submissions/6d781852-86ee-4c31-b533-480030ed3bdb

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_deletePositions_take_succ
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_deletePositions_take

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) {a : ℕ} (hD : a ∉ D) (ha : a < w.length) :
    (deletePositions w D)[retainedCount D a]? = w[a]? := by
  have h1 := deletePositions_take w (D := D) (show a + 1 ≤ w.length by omega)
  rw [deletePositions_take_succ, if_neg hD, List.getElem?_eq_getElem ha, Option.toList_some,
    retainedCount_succ_of_not_mem hD] at h1
  have h2 : (deletePositions (w.take a) D).length = retainedCount D a := by
    rw [length_deletePositions, List.length_take, min_eq_left ha.le]
  have := congrArg (fun u : List α => u[retainedCount D a]?) h1
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_append_right (by omega), h2,
    Nat.sub_self] at this
  rw [this, List.getElem?_eq_getElem ha]
  rfl
end DeciSigma1.Words
