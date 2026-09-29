-- Prove2me | solution 1 for TSPHeuristics.Insertion.insCost_le_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:14:54.806983+00:00
-- url     : https://prove2.me/submissions/1d09a515-efff-4296-88e4-2ffc36a53e95

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

open TSPHeuristics.Shared

lemma aux_icLO_path {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (F : ℕ → Fin n)
    (p q : ℕ) (hpq : p ≤ q) :
    d (F p) (F q) ≤ ∑ j ∈ Finset.Ico p q, d (F j) (F (j + 1)) := by
  induction q, hpq using Nat.le_induction with
  | base => simp [hd.diag]
  | succ q hpq ih =>
    rw [Finset.sum_Ico_succ_top hpq]
    linarith [hd.triangle (F p) (F q) (F (q + 1))]

lemma aux_icLO_two_le_tour {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (τ : Equiv.Perm (Fin n)) (x y : Fin n) :
    2 * d x y ≤ tourLength d τ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := x.pos; omega⟩
  set F : ℕ → Fin (m + 1) := fun j => τ ⟨j % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ with hF
  have htour : tourLength d τ = ∑ j ∈ Finset.range (m + 1), d (F j) (F (j + 1)) := by
    unfold tourLength
    rw [← Fin.sum_univ_eq_sum_range (fun j => d (F j) (F (j + 1)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e1 : (⟨k.val % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ : Fin (m + 1)) = k := by
      ext; simp [Nat.mod_eq_of_lt k.isLt]
    have e2 : (⟨(k.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ : Fin (m + 1)) =
        finRotate (m + 1) k := by
      ext; simp [finRotate_apply, Fin.val_add]
    simp only [hF, e1, e2]
  have key : ∀ x y : Fin (m + 1), (τ.symm x).val ≤ (τ.symm y).val →
      2 * d x y ≤ ∑ j ∈ Finset.range (m + 1), d (F j) (F (j + 1)) := by
    intro x y hle
    have hq : (τ.symm y).val ≤ m + 1 := (τ.symm y).isLt.le
    have hFp : F (τ.symm x).val = x := by
      simp only [hF, Nat.mod_eq_of_lt (τ.symm x).isLt]; simp
    have hFq : F (τ.symm y).val = y := by
      simp only [hF, Nat.mod_eq_of_lt (τ.symm y).isLt]; simp
    have hFn : F (m + 1) = F 0 := by simp [hF]
    have h1 := aux_icLO_path d hd F 0 (τ.symm x).val (Nat.zero_le _)
    have h2 := aux_icLO_path d hd F (τ.symm x).val (τ.symm y).val hle
    have h3 := aux_icLO_path d hd F (τ.symm y).val (m + 1) hq
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (τ.symm x).val) (hle.trans hq),
      ← Finset.sum_Ico_consecutive _ hle hq]
    rw [hFp] at h1 h2
    rw [hFq] at h2 h3
    rw [hFn] at h3
    have := hd.triangle y (F 0) x
    have := hd.symm x y
    have := hd.symm (F 0) x
    linarith
  rw [htour]
  rcases le_total (τ.symm x).val (τ.symm y).val with h | h
  · exact key x y h
  · rw [hd.symm x y]; exact key y x h

lemma aux_icLO_two_le_opt {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (x y : Fin n) :
    2 * d x y ≤ optimal d :=
  Finset.le_inf' _ _ (fun τ _ => aux_icLO_two_le_tour d hd τ x y)

lemma aux_icLO_zip {n : ℕ} (d : Fin n → Fin n → ℝ) :
    ∀ (l : List (Fin n)) (x : Fin n), ∃ L C, ∀ e,
      (List.zipWith d (x :: l) (l ++ [e])).sum = C + d L e := by
  intro l
  induction l with
  | nil => intro x; exact ⟨x, 0, fun e => by simp⟩
  | cons y l ih =>
    intro x
    obtain ⟨L, C, h⟩ := ih y
    exact ⟨L, d x y + C, fun e => by simp [h]; ring⟩

lemma aux_icLO_main {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : List (Fin n)) (k : Fin n) : insCost d T k ≤ optimal d := by
  have h0 : insCost d T k ≤ cycleLength d (T.insertIdx 0 k) - cycleLength d T :=
    Finset.inf'_le _ (Finset.mem_range.2 (Nat.succ_pos _))
  rw [List.insertIdx_zero] at h0
  cases T with
  | nil =>
    have e : cycleLength d [k] - cycleLength d [] = 0 := by simp [cycleLength, hd.diag]
    have := aux_icLO_two_le_opt d hd k k
    rw [hd.diag] at this
    linarith
  | cons t rest =>
    obtain ⟨L, C, h⟩ := aux_icLO_zip d rest t
    have e1 : cycleLength d (k :: t :: rest) = d k t + (C + d L k) := by
      unfold cycleLength
      rw [List.rotate_cons_succ, List.rotate_zero, List.cons_append, List.zipWith_cons_cons,
        List.sum_cons, h]
    have e2 : cycleLength d (t :: rest) = C + d L t := by
      unfold cycleLength
      rw [List.rotate_cons_succ, List.rotate_zero, h]
    have := aux_icLO_two_le_opt d hd k t
    have := hd.triangle L t k
    have := hd.symm t k
    linarith

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    ∀ i : ℕ, 1 ≤ i → i < n → insCost d (T i) (a i) ≤ TSPHeuristics.Shared.optimal d := by
  intro i _ _
  exact aux_icLO_main d hd (T i) (a i)
