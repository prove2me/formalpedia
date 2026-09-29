-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_middle_local_facts_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:13:00.295163+00:00
-- url     : https://prove2.me/submissions/f4e25a61-29bd-49d0-8afc-4ccbba4b9945

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma braid_strand_eq_right_middle_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdx j = strandIdxSucc i := by
  apply Fin.ext
  simp [strandIdx, strandIdxSucc, hji]

lemma braid_three_distinct_01_right_middle_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdx i ≠ strandIdx j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, hji] at hv

lemma braid_three_distinct_02_right_middle_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdx i ≠ strandIdxSucc j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, strandIdxSucc, hji] at hv
  omega

lemma right_middle_a_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    rightBraidFun n i j q (strandIdx i) =
      twistPoint ((i : ℕ) + 3 / 2) (-1) (4 * q - 2) := by
  have hca : strandIdx i ≠ strandIdx j :=
    braid_three_distinct_01_right_middle_v1 i j hji
  have hcb : strandIdx i ≠ strandIdxSucc j :=
    braid_three_distinct_02_right_middle_v1 i j hji
  have hfix :
      (Equiv.swap (strandIdx j) (strandIdxSucc j)) (strandIdx i) = strandIdx i :=
    Equiv.swap_apply_of_ne_of_ne hca hcb
  rw [rightBraidFun]
  simp only [if_neg hq1, if_pos hq2, hfix]
  rw [halfTwistFun_of_eq (4 * q - 2) (by simp [strandIdx])]

lemma right_middle_b_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    rightBraidFun n i j q (strandIdxSucc i) = ((((i : ℕ) : ℝ) + 3 : ℝ) : ℂ) := by
  have hbc : strandIdxSucc i = strandIdx j :=
    (braid_strand_eq_right_middle_v1 i j hji).symm
  have hv : (strandIdxSucc j : ℕ) = (i : ℕ) + 2 := by
    simp [strandIdxSucc, hji]
  have h0 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) := by
    omega
  have h1 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) + 1 := by
    omega
  rw [rightBraidFun]
  simp only [if_neg hq1, if_pos hq2]
  rw [hbc, Equiv.swap_apply_left]
  rw [halfTwistFun_of_fixed (4 * q - 2) h0 h1]
  rw [hv]
  push_cast
  ring

lemma right_middle_c_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    rightBraidFun n i j q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 3 / 2) 1 (4 * q - 2) := by
  have hbc : strandIdx j = strandIdxSucc i :=
    braid_strand_eq_right_middle_v1 i j hji
  rw [rightBraidFun]
  simp only [if_neg hq1, if_pos hq2]
  rw [Equiv.swap_apply_right, hbc]
  rw [halfTwistFun_of_eq_succ (4 * q - 2)
    (by simp [strandIdxSucc]) (by simp [strandIdxSucc])]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdx i) =
          twistPoint ((i : ℕ) + 3 / 2) (-1) (4 * q - 2)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc i) = ((((i : ℕ) : ℝ) + 3 : ℝ) : ℂ)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc j) =
          twistPoint ((i : ℕ) + 3 / 2) 1 (4 * q - 2)) := by
  intro n i j hji
  exact ⟨
    fun q hq1 hq2 => right_middle_a_v1 i j hji q hq1 hq2,
    ⟨fun q hq1 hq2 => right_middle_b_v1 i j hji q hq1 hq2,
      fun q hq1 hq2 => right_middle_c_v1 i j hji q hq1 hq2⟩
  ⟩
