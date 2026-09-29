-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_final_local_facts_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:17:06.999329+00:00
-- url     : https://prove2.me/submissions/662930d4-d79e-40be-814b-e121a6b24199

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma braid_strand_eq_right_final_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdx j = strandIdxSucc i := by
  apply Fin.ext
  simp [strandIdx, strandIdxSucc, hji]

lemma braid_three_distinct_01_right_final_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdx i ≠ strandIdx j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, hji] at hv

lemma braid_three_distinct_02_right_final_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdx i ≠ strandIdxSucc j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, strandIdxSucc, hji] at hv
  omega

lemma right_final_a_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    rightBraidFun n i j q (strandIdx i) =
      twistPoint ((i : ℕ) + 5 / 2) (-1) (4 * q - 3) := by
  have hca : strandIdx i ≠ strandIdx j :=
    braid_three_distinct_01_right_final_v1 i j hji
  have hcb : strandIdx i ≠ strandIdxSucc j :=
    braid_three_distinct_02_right_final_v1 i j hji
  have hfix :
      (Equiv.swap (strandIdx j) (strandIdxSucc j)) (strandIdx i) = strandIdx i :=
    Equiv.swap_apply_of_ne_of_ne hca hcb
  rw [rightBraidFun]
  simp only [if_neg hq1, if_neg hq2, hfix, Equiv.swap_apply_left]
  rw [halfTwistFun_of_eq (4 * q - 3) (by simp [strandIdxSucc, hji])]
  have hc : ((j : ℕ) : ℝ) + 3 / 2 = ((i : ℕ) : ℝ) + 5 / 2 := by
    rw [hji]
    push_cast
    ring
  rw [hc]

lemma right_final_b_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    rightBraidFun n i j q (strandIdxSucc i) =
      twistPoint ((i : ℕ) + 5 / 2) 1 (4 * q - 3) := by
  have hbc : strandIdxSucc i = strandIdx j :=
    (braid_strand_eq_right_final_v1 i j hji).symm
  have hca : strandIdxSucc j ≠ strandIdx i :=
    (braid_three_distinct_02_right_final_v1 i j hji).symm
  have hcb : strandIdxSucc j ≠ strandIdxSucc i := by
    intro h
    have hv := congrArg Fin.val h
    simp [strandIdxSucc, hji] at hv
  have hinner :
      (Equiv.swap (strandIdx j) (strandIdxSucc j)) (strandIdxSucc i) =
        strandIdxSucc j := by
    rw [hbc, Equiv.swap_apply_left]
  have hfix :
      (Equiv.swap (strandIdx i) (strandIdxSucc i)) (strandIdxSucc j) =
        strandIdxSucc j :=
    Equiv.swap_apply_of_ne_of_ne hca hcb
  rw [rightBraidFun]
  simp only [if_neg hq1, if_neg hq2, hinner, hfix]
  rw [halfTwistFun_of_eq_succ (4 * q - 3)
    (by simp [strandIdxSucc]) (by simp [strandIdxSucc])]
  have hc : ((j : ℕ) : ℝ) + 3 / 2 = ((i : ℕ) : ℝ) + 5 / 2 := by
    rw [hji]
    push_cast
    ring
  rw [hc]

lemma right_final_c_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    rightBraidFun n i j q (strandIdxSucc j) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by
  have hbc : strandIdx j = strandIdxSucc i :=
    braid_strand_eq_right_final_v1 i j hji
  have hv : (strandIdx i : ℕ) = (i : ℕ) := by
    simp [strandIdx]
  have h0 : (strandIdx i : ℕ) ≠ (j : ℕ) := by
    omega
  have h1 : (strandIdx i : ℕ) ≠ (j : ℕ) + 1 := by
    omega
  rw [rightBraidFun]
  simp only [if_neg hq1, if_neg hq2]
  rw [Equiv.swap_apply_right, hbc, Equiv.swap_apply_right]
  rw [halfTwistFun_of_fixed (4 * q - 3) h0 h1]
  rw [hv]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdx i) =
          twistPoint ((i : ℕ) + 5 / 2) (-1) (4 * q - 3)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc i) =
          twistPoint ((i : ℕ) + 5 / 2) 1 (4 * q - 3)) ∧
      (∀ (q : ℝ), ¬ q ≤ 1 / 2 → ¬ q ≤ 3 / 4 →
        rightBraidFun n i j q (strandIdxSucc j) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ)) := by
  intro n i j hji
  exact ⟨
    fun q hq1 hq2 => right_final_a_v1 i j hji q hq1 hq2,
    ⟨fun q hq1 hq2 => right_final_b_v1 i j hji q hq1 hq2,
      fun q hq1 hq2 => right_final_c_v1 i j hji q hq1 hq2⟩
  ⟩
