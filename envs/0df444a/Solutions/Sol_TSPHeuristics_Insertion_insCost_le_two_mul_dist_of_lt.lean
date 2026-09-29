-- Prove2me | solution 1 for TSPHeuristics.Insertion.insCost_le_two_mul_dist_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:42:08.438472+00:00
-- url     : https://prove2.me/submissions/12da567c-8f01-42e5-8575-a43b13c1dff2

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

theorem aux_icl2_cycle_rotate {n : ℕ} (d : Fin n → Fin n → ℝ) (L : List (Fin n)) (m : ℕ) :
    TSPHeuristics.Shared.cycleLength d (L.rotate m) = TSPHeuristics.Shared.cycleLength d L := by
  unfold TSPHeuristics.Shared.cycleLength
  have h1 : (L.rotate m).rotate 1 = (L.rotate 1).rotate m := by
    rw [List.rotate_rotate, List.rotate_rotate, Nat.add_comm]
  rw [h1, ← List.zipWith_rotate_distrib _ _ _ _ (by simp)]
  exact (List.rotate_perm _ _).sum_eq

theorem aux_icl2_cons_split {n : ℕ} (d : Fin n → Fin n → ℝ) (y x : Fin n) (C : List (Fin n)) :
    (List.zipWith d (y :: C) (C ++ [x])).sum
      = d y ((C ++ [x]).head (by simp)) + (List.zipWith d C (C ++ [x]).tail).sum := by
  cases C with
  | nil => simp
  | cons c C' => simp

theorem aux_icl2_insert_after {n : ℕ} (k x : Fin n) (s t : List (Fin n)) :
    (s ++ x :: t).insertIdx (s.length + 1) k = s ++ x :: k :: t := by
  induction s with
  | nil => simp
  | cons y s ih => simp [ih]

theorem aux_icl2_lemma2 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : List (Fin n)) (k x : Fin n) (hx : x ∈ T) : insCost d T k ≤ 2 * d k x := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
  have hmem : s.length + 1 ∈ Finset.range ((s ++ x :: t).length + 1) := by
    simp only [Finset.mem_range, List.length_append, List.length_cons]; omega
  refine le_trans (Finset.inf'_le _ hmem) ?_
  rw [aux_icl2_insert_after]
  have e1 : TSPHeuristics.Shared.cycleLength d (s ++ x :: k :: t)
      = TSPHeuristics.Shared.cycleLength d (x :: k :: (t ++ s)) := by
    rw [← aux_icl2_cycle_rotate d (s ++ x :: k :: t) s.length, List.rotate_append_length_eq]
    simp
  have e2 : TSPHeuristics.Shared.cycleLength d (s ++ x :: t)
      = TSPHeuristics.Shared.cycleLength d (x :: (t ++ s)) := by
    rw [← aux_icl2_cycle_rotate d (s ++ x :: t) s.length, List.rotate_append_length_eq]
    simp
  rw [e1, e2]
  set C := t ++ s
  unfold TSPHeuristics.Shared.cycleLength
  have r1 : (x :: k :: C).rotate 1 = k :: (C ++ [x]) := by simp
  have r2 : (x :: C).rotate 1 = C ++ [x] := by simp
  rw [r1, r2, List.zipWith_cons_cons, List.sum_cons, aux_icl2_cons_split, aux_icl2_cons_split]
  have htri := hd.triangle k x ((C ++ [x]).head (by simp))
  have hs := hd.symm x k
  linarith

theorem aux_icl2_mem {n : ℕ} (d : Fin n → Fin n → ℝ)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    ∀ i, 1 ≤ i → i ≤ n → ∀ j, j < i → a j ∈ T i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _ j hj
    rw [hrun.1]
    have : j = 0 := by omega
    subst this
    simp
  | succ i hi ih =>
    intro hin j hj
    obtain ⟨_, pos, hpos, heq, _⟩ := hrun.2 i hi (by omega)
    rw [heq, List.mem_insertIdx hpos]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact Or.inr (ih (by omega) j h)
    · exact Or.inl (by rw [h])

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    ∀ i j : ℕ, j < i → i < n → insCost d (T i) (a i) ≤ 2 * d (a i) (a j) := by
  intro i j hji hin
  exact aux_icl2_lemma2 d hd (T i) (a i) (a j)
    (aux_icl2_mem d T a hrun i (by omega) (by omega) j hji)
