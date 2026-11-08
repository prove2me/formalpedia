-- Prove2me | solution 1 for WagerFairDiv.theorem_3_pareto_of_sideBetPO
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:02:32.211638+00:00
-- url     : https://prove2.me/submissions/62bca9e2-7b35-445b-9ab1-0efc6d74e971

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A)
    (hAB : Corresponding A B) (hSB : SideBetPO B) (hBB : BBOnSupport B) :
    ParetoOptimal A := by
  classical
  intro v e a' ha' ⟨i1, hi1⟩
  by_contra hcon
  push_neg at hcon
  set T := e.total with hT
  have hTpos : 0 < T := by
    rw [hT]; unfold PosVec.total
    exact Finset.sum_pos (fun i _ => e.2 i) ⟨i1, Finset.mem_univ _⟩
  set S : Fin m → Prop := fun j => ∃ i, 0 < (v i).1 j with hS
  have hvnn : ∀ i j, 0 ≤ (v i).1 j := fun i j => (v i).2.1 j
  have hv0 : ∀ i j, ¬ S j → (v i).1 j = 0 := by
    intro i j hj
    rcases (hvnn i j).eq_or_lt with h | h
    · exact h.symm
    · exact absurd ⟨i, h⟩ hj
  have hsumA : ∀ j, S j → ∑ i, A v e i j = 1 := by
    intro j hj
    have h := hBB v e j hj
    simp only [hAB v e] at h
    rw [← Finset.mul_sum] at h
    have : T * (∑ i, A v e i j) = T * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel₀ hTpos.ne' this
  set db : Fin n → Fin m → ℝ := fun i j =>
    if S j then T * (a' i j - A v e i j) + (if i = i1 then T * (1 - ∑ k, a' k j) else 0)
    else 0 with hdb
  apply hSB v e
  refine ⟨db, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [hdb]
    by_cases hj : S j
    · simp only [hj, if_true]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i1, if_pos (Finset.mem_univ _),
        ← Finset.mul_sum, Finset.sum_sub_distrib, hsumA j hj]
      ring
    · simp [hj]
  · intro i j
    rw [hAB v e i j]
    simp only [hdb]
    have hAnn := (hA v e).1 i j
    by_cases hj : S j
    · simp only [hj, if_true]
      have ha'nn := ha'.1 i j
      have hslack : 0 ≤ 1 - ∑ k, a' k j := by linarith [ha'.2 j]
      split_ifs
      · nlinarith [mul_nonneg hTpos.le hslack, mul_nonneg hTpos.le ha'nn]
      · nlinarith [mul_nonneg hTpos.le ha'nn]
    · simp only [hj, if_false, add_zero]
      exact mul_nonneg hTpos.le hAnn
  · have hval : ∀ i, val (v i).1 (db i) =
        T * (val (v i).1 (a' i) - val (v i).1 (A v e i)) +
          (if i = i1 then T * ∑ j, (v i).1 j * (1 - ∑ k, a' k j) else 0) := by
      intro i
      unfold val
      simp only [hdb]
      have hterm : ∀ j, (v i).1 j * (if S j then T * (a' i j - A v e i j) +
          (if i = i1 then T * (1 - ∑ k, a' k j) else 0) else 0) =
          T * ((v i).1 j * a' i j - (v i).1 j * A v e i j) +
            (if i = i1 then T * ((v i).1 j * (1 - ∑ k, a' k j)) else 0) := by
        intro j
        by_cases hj : S j
        · simp only [hj, if_true]; split_ifs <;> ring
        · simp only [hj, if_false, hv0 i j hj]; split_ifs <;> ring
      simp only [hterm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      split_ifs
      · rw [Finset.mul_sum]
      · simp
    intro i
    rw [hval i]
    have h1 := hcon i
    have h2 : 0 ≤ ∑ j, (v i).1 j * (1 - ∑ k, a' k j) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hvnn i j) (by linarith [ha'.2 j]))
    have h3 : 0 ≤ T * (val (v i).1 (a' i) - val (v i).1 (A v e i)) :=
      mul_nonneg hTpos.le (by linarith)
    split_ifs
    · nlinarith [mul_nonneg hTpos.le h2]
    · linarith
  · refine ⟨i1, ?_⟩
    have hval1 : val (v i1).1 (db i1) =
        T * (val (v i1).1 (a' i1) - val (v i1).1 (A v e i1)) +
          T * ∑ j, (v i1).1 j * (1 - ∑ k, a' k j) := by
      unfold val
      simp only [hdb, if_true]
      have hterm : ∀ j, (v i1).1 j * (if S j then T * (a' i1 j - A v e i1 j) +
          T * (1 - ∑ k, a' k j) else 0) =
          T * ((v i1).1 j * a' i1 j - (v i1).1 j * A v e i1 j) +
            T * ((v i1).1 j * (1 - ∑ k, a' k j)) := by
        intro j
        by_cases hj : S j
        · simp only [hj, if_true]; ring
        · simp only [hj, if_false, hv0 i1 j hj]; ring
      simp only [hterm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hval1]
    have h2 : 0 ≤ ∑ j, (v i1).1 j * (1 - ∑ k, a' k j) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hvnn i1 j) (by linarith [ha'.2 j]))
    have h3 : 0 < T * (val (v i1).1 (a' i1) - val (v i1).1 (A v e i1)) :=
      mul_pos hTpos (by linarith)
    nlinarith [mul_nonneg hTpos.le h2]
