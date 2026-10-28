-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.sorted_roots
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:56:01.886676+00:00
-- url     : https://prove2.me/submissions/6cb89449-540d-4873-9222-b119c285138e

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial

lemma S171Q_cross {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (p : Polynomial R) (a c x : R) (hx : x ∈ crossingRoot p a c) : a < x ∧ x < c := by
  unfold crossingRoot at hx
  split_ifs at hx with h1 h2
  · simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨ha, hb, he⟩ := (PolynomialIVT.root p a c h1.1 (le_of_lt h1.2.1) (le_of_lt h1.2.2)).property
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · intro h; rw [← h] at he; exact absurd he h1.2.1.ne
    · intro h; rw [h] at he; exact absurd he h1.2.2.ne'
  · simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨ha, hb, he⟩ := (PolynomialIVT.root (-p) a c h2.1 (le_of_lt h2.2.1) (le_of_lt h2.2.2)).property
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · intro h; rw [← h] at he; exact absurd he h2.2.1.ne
    · intro h; rw [h] at he; exact absurd he h2.2.2.ne'
  · simp at hx

lemma S171Q_cross_pw {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (p : Polynomial R) (a c : R) : (crossingRoot p a c).Pairwise (· < ·) := by
  unfold crossingRoot
  split_ifs <;> simp

lemma S171Q_scan {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (p : Polynomial R) (cs : List R) : ∀ a : R, (a :: cs).Pairwise (· < ·) →
    (scanCells p a cs).Pairwise (· < ·) ∧ ∀ x ∈ scanCells p a cs, a < x := by
  induction cs with
  | nil => intro a _; simp [scanCells]
  | cons c cs ih =>
    intro a h
    have hac : a < c := List.rel_of_pairwise_cons h (by simp)
    obtain ⟨ih1, ih2⟩ := ih c (List.Pairwise.of_cons h)
    have hmid : ∀ x ∈ (if p.eval c = 0 then [c] else []), x = c := by
      intro x hx; split_ifs at hx <;> simp_all
    have hmidpw : (if p.eval c = 0 then [c] else []).Pairwise (· < ·) := by split_ifs <;> simp
    simp only [scanCells]
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨S171Q_cross_pw p a c, hmidpw, ?_⟩, ih1, ?_⟩
      · intro x hx y hy
        rw [hmid y hy]; exact (S171Q_cross p a c x hx).2
      · intro x hx y hy
        rcases List.mem_append.1 hx with hx | hx
        · exact lt_trans (S171Q_cross p a c x hx).2 (ih2 y hy)
        · rw [hmid x hx]; exact ih2 y hy
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · exact (S171Q_cross p a c x hx).1
        · rw [hmid x hx]; exact hac
      · exact lt_trans hac (ih2 x hx)

lemma S171Q_aux {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (a b : R) (n : ℕ) : ∀ p : Polynomial R, (rootsAux n p a b).Pairwise (· < ·) ∧
      ∀ x ∈ rootsAux n p a b, a < x ∧ x < b := by
  induction n with
  | zero => intro p; simp [rootsAux]
  | succ n ih =>
    intro p
    simp only [rootsAux]
    split_ifs with h
    · simp
    · push Not at h
      obtain ⟨ih1, ih2⟩ := ih p.derivative
      have hpw : (a :: (rootsAux n p.derivative a b ++ [b])).Pairwise (· < ·) := by
        rw [List.pairwise_cons, List.pairwise_append]
        refine ⟨?_, ih1, by simp, ?_⟩
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact (ih2 x hx).1
          · simp at hx; rw [hx]; exact h.2
        · intro x hx y hy
          simp at hy; rw [hy]; exact (ih2 x hx).2
      refine ⟨(S171Q_scan p _ a hpw).1.filter _, ?_⟩
      intro x hx
      simpa using (List.mem_filter.1 hx).2

theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p : Polynomial R) :
    (roots p a b).Pairwise (· < ·) := by
  exact (S171Q_aux a b _ p).1

end
