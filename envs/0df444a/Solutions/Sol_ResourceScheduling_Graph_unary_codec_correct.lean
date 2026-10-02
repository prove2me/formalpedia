-- Prove2me | solution 1 for ResourceScheduling.Graph.unary_codec_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T05:46:36.462849+00:00
-- url     : https://prove2.me/submissions/79e4a4d1-94b0-4b42-bf3e-4f1353c69e02

import Definitions.Def_ResourceScheduling_Graph_Codec

set_option autoImplicit false

open ResourceScheduling.Graph

private theorem readUnary_append (n : ℕ) (rest : List Letter) :
    readUnary (unary n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [unary, readUnary]
  | succ n ih =>
    simp [unary, List.replicate_succ, readUnary] at ih ⊢
    simp [ih]

private theorem unary_append_injective {n m : ℕ} {xs ys : List Letter}
    (h : unary n ++ xs = unary m ++ ys) : n = m ∧ xs = ys := by
  have e := congrArg readUnary h
  simpa only [readUnary_append, Option.some.injEq, Prod.mk.injEq] using e

private theorem readUnary_sound (w : List Letter) (n : ℕ) (rest : List Letter)
    (h : readUnary w = some (n, rest)) : w = unary n ++ rest := by
  induction w generalizing n rest with
  | nil => simp [readUnary] at h
  | cons a w ih =>
    cases a with
    | sep =>
      simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [unary]
    | one =>
      cases hw : readUnary w with
      | none => simp [readUnary, hw] at h
      | some p =>
        obtain ⟨m, tail⟩ := p
        simp [readUnary, hw] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih m tail hw]
        simp [unary, List.replicate_succ, List.append_assoc]

private theorem encNatList_injective : Function.Injective encNatList := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      have := congrArg List.length h
      simp [encNatList, unary] at this
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have := congrArg List.length h
      simp [encNatList, unary] at this
    | cons y ys =>
      have hp : unary x ++ encNatList xs = unary y ++ encNatList ys := h
      obtain ⟨hxy, htail⟩ := unary_append_injective hp
      exact congrArg₂ List.cons hxy (ih htail)

/-- Decoding is exact on arbitrary suffixes, successful decoding reconstructs the input,
and concatenated unary codes uniquely determine their natural-number list. -/
theorem solution :
    (∀ n rest, readUnary (unary n ++ rest) = some (n, rest)) ∧
    (∀ w n rest, readUnary w = some (n, rest) → w = unary n ++ rest) ∧
    Function.Injective encNatList := by
  exact ⟨readUnary_append, readUnary_sound, encNatList_injective⟩

#print axioms solution
