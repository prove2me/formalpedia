-- Prove2me | solution 1 for TSPHeuristics.Insertion.lemma_2_insCost_le_two_mul_dist
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:34:53.099716+00:00
-- url     : https://prove2.me/submissions/ae00a6c9-5a13-4775-84ef-68fc5f884bc5

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Sum of the path `b, l₀, …, l_{m-1}` followed by the closing edge to `a`. -/
noncomputable def aux_l2ins_f {n : ℕ} (d : Fin n → Fin n → ℝ) (b : Fin n) (l : List (Fin n))
    (a : Fin n) : ℝ :=
  (List.zipWith d (b :: l) (l ++ [a])).sum

theorem aux_l2ins_f_nil {n : ℕ} (d : Fin n → Fin n → ℝ) (b a : Fin n) :
    aux_l2ins_f d b [] a = d b a := by
  simp [aux_l2ins_f]

theorem aux_l2ins_f_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (b c : Fin n) (l : List (Fin n))
    (a : Fin n) : aux_l2ins_f d b (c :: l) a = d b c + aux_l2ins_f d c l a := by
  simp [aux_l2ins_f]

theorem aux_l2ins_f_le {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (l : List (Fin n)) : ∀ (b a a' : Fin n),
    aux_l2ins_f d b l a ≤ aux_l2ins_f d b l a' + d a' a := by
  induction l with
  | nil =>
    intro b a a'
    rw [aux_l2ins_f_nil, aux_l2ins_f_nil]
    exact hd.triangle b a' a
  | cons c l ih =>
    intro b a a'
    rw [aux_l2ins_f_cons, aux_l2ins_f_cons]
    have := ih c a a'
    linarith

theorem aux_l2ins_cycle_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (b : Fin n) (l : List (Fin n)) :
    TSPHeuristics.Shared.cycleLength d (b :: l) = aux_l2ins_f d b l b := by
  simp [TSPHeuristics.Shared.cycleLength, aux_l2ins_f]

theorem aux_l2ins_cycle_rotate {n : ℕ} (d : Fin n → Fin n → ℝ) (l : List (Fin n)) (r : ℕ) :
    TSPHeuristics.Shared.cycleLength d (l.rotate r) = TSPHeuristics.Shared.cycleLength d l := by
  unfold TSPHeuristics.Shared.cycleLength
  have h1 : (l.rotate r).rotate 1 = (l.rotate 1).rotate r := by
    rw [List.rotate_rotate, List.rotate_rotate, Nat.add_comm]
  rw [h1, ← List.zipWith_rotate_distrib _ _ _ _ (by simp)]
  exact (List.rotate_perm _ _).sum_eq

theorem aux_l2ins_cycle_swap {n : ℕ} (d : Fin n → Fin n → ℝ) (L M : List (Fin n)) :
    TSPHeuristics.Shared.cycleLength d (L ++ M) = TSPHeuristics.Shared.cycleLength d (M ++ L) := by
  rw [← List.rotate_append_length_eq L M, aux_l2ins_cycle_rotate]

theorem aux_l2ins_insertIdx_append {α : Type*} (L M : List α) (k : α) :
    (L ++ M).insertIdx L.length k = L ++ k :: M := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.cons_append, List.length_cons]
    rw [List.insertIdx_succ_cons, ih]

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : List (Fin n)) (hT : T.Nodup) (k j : Fin n) (hk : k ∉ T) (hj : j ∈ T) :
    insCost d T k ≤ 2 * d k j := by
  obtain ⟨L, R, rfl⟩ := List.append_of_mem hj
  have hpos : L.length ∈ Finset.range ((L ++ j :: R).length + 1) := by
    rw [Finset.mem_range]; simp
  refine le_trans (Finset.inf'_le _ hpos) ?_
  show TSPHeuristics.Shared.cycleLength d ((L ++ j :: R).insertIdx L.length k) -
    TSPHeuristics.Shared.cycleLength d (L ++ j :: R) ≤ 2 * d k j
  rw [aux_l2ins_insertIdx_append, aux_l2ins_cycle_swap d L (k :: j :: R),
    aux_l2ins_cycle_swap d L (j :: R)]
  simp only [List.cons_append]
  rw [aux_l2ins_cycle_cons, aux_l2ins_cycle_cons, aux_l2ins_f_cons]
  have h := aux_l2ins_f_le d hd (R ++ L) j k j
  have hs := hd.symm j k
  linarith
