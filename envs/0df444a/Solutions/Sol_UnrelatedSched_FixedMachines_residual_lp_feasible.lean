-- Prove2me | solution 1 for UnrelatedSched.FixedMachines.residual_lp_feasible
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:48:38.36439+00:00
-- url     : https://prove2.me/submissions/c4ce1026-0db2-40d1-a7d4-d930590c144b

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
open UnrelatedSched.FixedMachines MatousekLP.Scheduling


open MatousekLP.Scheduling

/-- §3, p. 6: if `σ` is a schedule with makespan at most `d`, then its long assignments
(`L j = some (σ j)` exactly when `p_{σ(j) j} > ε d`) form an admissible schedule of long
assignments, and the 0-1 matrix of `σ` on the remaining jobs is a feasible solution of the
residual LP with `d_i = d - t_i` and `t = ε d`. -/
theorem solution {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε) (d : ℕ) (σ : Fin n → Fin m)
    (hσ : makespan (fun i j => (P i j : ℝ)) σ ≤ (d : ℝ)) :
    let L : Fin n → Option (Fin m) :=
      fun j => if ε * (d : ℝ) < (P (σ j) j : ℝ) then some (σ j) else none
    IsAdmissible P ε d L ∧
      (fun i j => if L j = none ∧ σ j = i then (1 : ℝ) else 0) ∈ ResidualLP P ε d L := by
  classical
  dsimp only
  let L : Fin n → Option (Fin m) :=
    fun j => if ε * (d : ℝ) < (P (σ j) j : ℝ) then some (σ j) else none
  change IsAdmissible P ε d L ∧
    (fun i j => if L j = none ∧ σ j = i then (1 : ℝ) else 0) ∈ ResidualLP P ε d L
  have hfollow : ∀ j i, L j = some i → σ j = i := by
    intro j i hj
    dsimp [L] at hj
    split_ifs at hj with h
    exact Option.some.inj hj
  have hload : ∀ i, load (fun i j => (P i j : ℝ)) σ i ≤ (d : ℝ) := by
    intro i
    exact (le_ciSup (Finite.bddAbove_range _) i).trans hσ
  have hdecomp : ∀ i, load (fun i j => (P i j : ℝ)) σ i =
      longLoad P L i + shortLoad P L σ i := by
    intro i
    simp only [load, longLoad, shortLoad, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    cases hl : L j with
    | none => simp [hl]
    | some a =>
      have hf := hfollow j a hl
      by_cases ha : a = i
      · simp [hl, hf, ha]
      · have hsi : σ j ≠ i := by simpa [hf] using ha
        simp [hl, ha, hsi]
  have hlong : ∀ i, longLoad P L i ≤ (d : ℝ) := by
    intro i
    have hn : 0 ≤ shortLoad P L σ i := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hh := hload i
    rw [hdecomp i] at hh
    linarith
  constructor
  · constructor
    · intro j i hj
      dsimp [L] at hj
      split_ifs at hj with ht
      cases Option.some.inj hj
      exact ht
    · exact hlong
  · change _ ∈ DeadlineLP P {j | L j = none} _ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      dsimp only
      split_ifs <;> norm_num
    · intro i j hij
      by_cases hc : L j = none ∧ σ j = i
      · have hsij := hc.2
        have : L j ≠ none := by simp [L, hsij, hij]
        exact False.elim (this hc.1)
      · simp [hc]
    · intro i j hj
      simp only [Set.mem_setOf_eq] at hj
      simp [hj]
    · intro j hj
      simp only [Set.mem_setOf_eq] at hj
      simp [hj, Finset.sum_ite_eq', eq_comm]
    · intro i
      have he : (∑ j : Fin n, (P i j : ℝ) *
          if L j = none ∧ σ j = i then 1 else 0) = shortLoad P L σ i := by
        simp [shortLoad, Finset.sum_filter, mul_ite]
      rw [he]
      have hh := hload i
      rw [hdecomp i] at hh
      linarith



#print axioms solution
