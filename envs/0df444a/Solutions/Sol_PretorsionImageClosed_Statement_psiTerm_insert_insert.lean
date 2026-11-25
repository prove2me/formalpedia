-- Prove2me | solution 1 for PretorsionImageClosed.Statement.psiTerm_insert_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:21:29.153935+00:00
-- url     : https://prove2.me/submissions/956fff46-1813-4fb4-b6ce-2292f48f99d0

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {r : ι} {R Cont : Finset ι} (hr : ∀ x ∈ R, x < r)
    (hCont : Cont ⊆ R) :
    psiTerm (insert r R) (insert r Cont) =
      X * (C q * psiTerm R Cont + if Cont = R then X ^ R.card else 0) := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  have hrC : r ∉ Cont := fun h => hrR (hCont h)
  have hlt : ∀ e ∈ Cont, e < r := fun e he => hr e (hCont he)
  -- the filtered set of admissible pivots
  have hfilter : (insert r Cont).filter (fun e => ∀ a ∈ insert r R, a < e → a ∈ insert r Cont) =
      (if Cont = R then insert r (Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont))
        else Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont)) := by
    rw [Finset.filter_insert]
    have hsame : Cont.filter (fun e => ∀ a ∈ insert r R, a < e → a ∈ insert r Cont) =
        Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont) := by
      apply Finset.filter_congr
      intro e he
      constructor
      · intro h a ha hae
        rcases Finset.mem_insert.1 (h a (Finset.mem_insert_of_mem ha) hae) with rfl | h'
        · exact absurd hae (not_lt.2 (hlt e he).le)
        · exact h'
      · intro h a ha hae
        rcases Finset.mem_insert.1 ha with rfl | ha'
        · exact absurd hae (not_lt.2 (hlt e he).le)
        · exact Finset.mem_insert_of_mem (h a ha' hae)
    rw [hsame]
    by_cases hCR : Cont = R
    · rw [if_pos hCR, if_pos]
      intro a ha _
      rcases Finset.mem_insert.1 ha with rfl | ha'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hCR ▸ ha')
    · rw [if_neg hCR, if_neg]
      intro h
      apply hCR
      apply Finset.Subset.antisymm hCont
      intro a ha
      rcases Finset.mem_insert.1 (h a (Finset.mem_insert_of_mem ha) (hr a ha)) with rfl | h'
      · exact absurd ha hrR
      · exact h'
  -- the count of continued rows after a pivot
  have hcount : ∀ e ∈ Cont, ((insert r Cont).filter (fun a => e < a)).card =
      (Cont.filter (fun a => e < a)).card + 1 := by
    intro e he
    rw [Finset.filter_insert, if_pos (hlt e he), Finset.card_insert_of_notMem]
    intro h
    exact hrC (Finset.mem_filter.1 h).1
  have hcount_r : ((insert r Cont).filter (fun a => r < a)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · exact lt_irrefl _
    · exact not_lt.2 (hlt a ha').le
  unfold psiTerm
  rw [hfilter, Finset.card_insert_of_notMem hrC]
  have hnotmem : r ∉ Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont) :=
    fun h => hrC (Finset.mem_filter.1 h).1
  by_cases hCR : Cont = R
  · rw [if_pos hCR, if_pos hCR, Finset.sum_insert hnotmem, hcount_r,
      Finset.sum_congr rfl (fun e he => by rw [hcount e (Finset.mem_filter.1 he).1])]
    subst hCR
    simp only [pow_zero, map_one, pow_succ, map_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => by rw [mul_comm (C (q ^ _)) (C q)])]
    rw [← Finset.mul_sum]
    ring
  · rw [if_neg hCR, if_neg hCR,
      Finset.sum_congr rfl (fun e he => by rw [hcount e (Finset.mem_filter.1 he).1])]
    simp only [pow_succ, map_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => by rw [mul_comm (C (q ^ _)) (C q)])]
    rw [← Finset.mul_sum]
    ring
end PretorsionImageClosed.Statement
