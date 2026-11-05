-- Prove2me | solution 1 for PancakeHard.property_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-04T08:18:36.071396+00:00
-- url     : https://prove2.me/submissions/853134b5-feed-4af3-a27f-1fc14316a4e9

import Mathlib
import Definitions.Def_PancakeHard_Basic

set_option autoImplicit false

namespace PancakeHard

private def pq (xy : ℕ × ℕ) : Bool := !(xy.1 + 1 == xy.2 || xy.2 + 1 == xy.1)

private def cc (L : List ℕ) : ℕ := (L.zip L.tail).countP pq

private lemma pq_symm (a b : ℕ) : pq (a, b) = pq (b, a) := by
  unfold pq; cases h1 : (a + 1 == b) <;> cases h2 : (b + 1 == a) <;> simp_all

private lemma cc_nil : cc [] = 0 := rfl
private lemma cc_single (a : ℕ) : cc [a] = 0 := rfl
private lemma cc_cons2 (a b : ℕ) (l : List ℕ) :
    cc (a :: b :: l) = cc (b :: l) + (if pq (a, b) then 1 else 0) := by
  simp [cc, List.countP_cons]

private lemma cc_append (A : List ℕ) (b : ℕ) (B : List ℕ) :
    cc (A ++ b :: B) = cc (A ++ [b]) + cc (b :: B) := by
  induction A with
  | nil => simp [cc_single]
  | cons a A ih =>
    cases A with
    | nil => simp [cc_cons2, cc_single]; omega
    | cons a' A'' =>
      simp only [List.cons_append] at ih ⊢
      rw [cc_cons2, cc_cons2, ih]; omega

private lemma cc_snoc (A : List ℕ) (a b : ℕ) :
    cc ((A ++ [a]) ++ [b]) = cc (A ++ [a]) + (if pq (a, b) then 1 else 0) := by
  rw [List.append_assoc, List.singleton_append, cc_append, cc_cons2, cc_single]; simp

private lemma cc_reverse (L : List ℕ) : cc L.reverse = cc L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases L with
    | nil => rfl
    | cons b L' =>
      rw [List.reverse_cons, List.reverse_cons, cc_snoc, ← List.reverse_cons, ih, cc_cons2, pq_symm]

private lemma bp_eq (S : List ℕ) : breakpoints S = cc S +
    (match S.getLast? with
     | none => 0
     | some x => if x = S.length then 0 else 1) := rfl

private lemma key (A B : List ℕ) (hAne : A ≠ []) :
    (breakpoints (A.reverse ++ B) : ℤ) - breakpoints (A ++ B) ∈ ({-1, 0, 1} : Set ℤ) := by
  have hlen : (A.reverse ++ B).length = (A ++ B).length := by simp
  rw [bp_eq, bp_eq, hlen]
  generalize (A ++ B).length = n
  obtain ⟨A0, aL, hAL⟩ : ∃ A0 aL, A = A0 ++ [aL] :=
    ⟨A.dropLast, A.getLast hAne, (List.dropLast_append_getLast hAne).symm⟩
  obtain ⟨a1, A1, hA1⟩ := List.exists_cons_of_ne_nil hAne
  cases B with
  | nil =>
    simp only [List.append_nil]
    rw [cc_reverse]
    generalize A.reverse.getLast? = o1
    generalize A.getLast? = o2
    rcases o1 with _ | x <;> rcases o2 with _ | y <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> (try split_ifs) <;> push_cast <;> omega
  | cons b B' =>
    have eX : ∀ X : List ℕ, (X ++ b :: B').getLast? = (b :: B').getLast? := by
      intro X
      cases hy : (b :: B').getLast? with
      | none => simp at hy
      | some y => rw [List.getLast?_append, hy]; rfl
    have e1 := eX A.reverse
    have e2 := eX A
    rw [e1, e2, cc_append, cc_append (A := A)]
    have h1 : cc (A.reverse ++ [b]) = cc A.reverse + (if pq (a1, b) then 1 else 0) := by
      rw [hA1, List.reverse_cons, cc_snoc]
    have h2 : cc (A ++ [b]) = cc A + (if pq (aL, b) then 1 else 0) := by
      rw [hAL, cc_snoc]
    rw [h1, h2, cc_reverse]
    generalize (b :: B').getLast? = o
    rcases o with _ | x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> split_ifs <;> push_cast <;> omega

theorem property_1_aux (S S' : List ℕ) (hS : IsStack S) (h : IsFlip S S') :
    (breakpoints S' : ℤ) - breakpoints S ∈ ({-1, 0, 1} : Set ℤ) := by
  obtain ⟨r, hr1, hr2, rfl⟩ := h
  have hne : S.take r ≠ [] := by
    intro h0
    rw [List.take_eq_nil_iff] at h0
    rcases h0 with h0 | h0
    · omega
    · subst h0; simp at hr2; omega
  have := key (S.take r) (S.drop r) hne
  rwa [List.take_append_drop] at this

end PancakeHard

theorem solution (S S' : List ℕ) (hS : PancakeHard.IsStack S) (h : PancakeHard.IsFlip S S') :
    (PancakeHard.breakpoints S' : ℤ) - PancakeHard.breakpoints S ∈ ({-1, 0, 1} : Set ℤ) :=
  PancakeHard.property_1_aux S S' hS h
