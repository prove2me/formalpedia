-- Prove2me | solution 1 for P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:57.154712+00:00
-- url     : https://prove2.me/submissions/b81624d6-82a4-435d-ac85-41ddc959817d

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_1824c702cd1d
public import Theorems.Thm_DeciSigma1_Words_le_greatestPreimage_iff
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_not_mem
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) (a : ℕ) :
    (deletePositions w D)[a]? = w[greatestPreimage D a]? := by
  rcases Nat.lt_or_ge (greatestPreimage D a) w.length with h | h
  · rw [← getElem?_deletePositions w (greatestPreimage_not_mem a) h, retainedCount_greatestPreimage]
  · rw [List.getElem?_eq_none h, List.getElem?_eq_none]
    rw [length_deletePositions]
    exact le_greatestPreimage_iff.mp h
end DeciSigma1.Words
