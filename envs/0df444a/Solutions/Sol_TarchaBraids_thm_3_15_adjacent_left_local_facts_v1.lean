-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_left_local_facts_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:40:23.987256+00:00
-- url     : https://prove2.me/submissions/3235ceeb-fe6e-4f2c-ae1a-84190679cf44

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_geometry_interfaces_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma braid_strand_eq_local {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : strandIdx j = strandIdxSucc i := by
  apply Fin.ext
  simp [strandIdx, strandIdxSucc, hji]

lemma braid_three_distinct_01 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : strandIdx i ≠ strandIdx j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, hji] at hv

lemma braid_three_distinct_02 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : strandIdx i ≠ strandIdxSucc j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, strandIdxSucc, hji] at hv
  omega

lemma leftBraidFun_first_a {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq : q ≤ 1 / 2) :
    leftBraidFun n i j q (strandIdx i) =
      twistPoint ((i : ℕ) + 3 / 2) (-1) (2 * q) := by
  rw [leftBraidFun]
  simp only [if_pos hq]
  rw [halfTwistFun_of_eq (2 * q) (by simp [strandIdx])]

lemma leftBraidFun_first_b {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq : q ≤ 1 / 2) :
    leftBraidFun n i j q (strandIdxSucc i) =
      twistPoint ((i : ℕ) + 3 / 2) 1 (2 * q) := by
  rw [leftBraidFun]
  simp only [if_pos hq]
  rw [halfTwistFun_of_eq_succ (2 * q) (by simp [strandIdxSucc]) (by simp [strandIdxSucc])]

lemma leftBraidFun_first_c {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) (hq : q ≤ 1 / 2) :
    leftBraidFun n i j q (strandIdxSucc j) = ((((i : ℕ) : ℝ) + 3 : ℝ) : ℂ) := by
  have hv : (strandIdxSucc j : ℕ) = (i : ℕ) + 2 := by
    simp [strandIdxSucc, hji]
  have h0 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) := by omega
  have h1 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) + 1 := by omega
  rw [leftBraidFun]
  simp only [if_pos hq]
  rw [halfTwistFun_of_fixed (2 * q) h0 h1]
  rw [hv]
  push_cast
  ring

lemma leftBraidFun_middle_a {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    leftBraidFun n i j q (strandIdx i) =
      twistPoint ((i : ℕ) + 5 / 2) (-1) (4 * q - 2) := by
  have hab : strandIdxSucc i = strandIdx j := (braid_strand_eq_local i j hji).symm
  rw [leftBraidFun]
  simp only [if_neg hq1, if_pos hq2]
  rw [Equiv.swap_apply_left, hab]
  rw [halfTwistFun_of_eq (4 * q - 2) (by simp [strandIdx])]
  have hc : ((j : ℕ) : ℝ) + 3 / 2 = ((i : ℕ) : ℝ) + 5 / 2 := by
    rw [hji]
    push_cast
    ring
  rw [hc]

lemma leftBraidFun_middle_b {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    leftBraidFun n i j q (strandIdxSucc i) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by
  have hv : (strandIdx i : ℕ) = (i : ℕ) := by simp [strandIdx]
  have h0 : (strandIdx i : ℕ) ≠ (j : ℕ) := by omega
  have h1 : (strandIdx i : ℕ) ≠ (j : ℕ) + 1 := by omega
  rw [leftBraidFun]
  simp only [if_neg hq1, if_pos hq2, Equiv.swap_apply_right]
  rw [halfTwistFun_of_fixed (4 * q - 2) h0 h1]
  rw [hv]

lemma leftBraidFun_middle_c {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    leftBraidFun n i j q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 5 / 2) 1 (4 * q - 2) := by
  have hca : strandIdxSucc j ≠ strandIdx i := (braid_three_distinct_02 i j hji).symm
  have hcb : strandIdxSucc j ≠ strandIdxSucc i := by
    intro h
    have hv := congrArg Fin.val h
    simp [strandIdxSucc, hji] at hv
  have hfix : (Equiv.swap (strandIdx i) (strandIdxSucc i)) (strandIdxSucc j) =
      strandIdxSucc j := Equiv.swap_apply_of_ne_of_ne hca hcb
  rw [leftBraidFun]
  simp only [if_neg hq1, if_pos hq2, hfix]
  rw [halfTwistFun_of_eq_succ (4 * q - 2)
    (by simp [strandIdxSucc]) (by simp [strandIdxSucc])]
  have hc : ((j : ℕ) : ℝ) + 3 / 2 = ((i : ℕ) : ℝ) + 5 / 2 := by
    rw [hji]
    push_cast
    ring
  rw [hc]

lemma leftBraidFun_final_a {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    leftBraidFun n i j q (strandIdx i) = ((((i : ℕ) : ℝ) + 3 : ℝ) : ℂ) := by
  have hbc : strandIdx j = strandIdxSucc i := braid_strand_eq_local i j hji
  have hv : (strandIdxSucc j : ℕ) = (i : ℕ) + 2 := by simp [strandIdxSucc, hji]
  have h0 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) := by omega
  have h1 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) + 1 := by omega
  rw [leftBraidFun]
  simp only [if_neg hq1, if_neg hq2]
  rw [Equiv.swap_apply_left, ← hbc, Equiv.swap_apply_left]
  rw [halfTwistFun_of_fixed (4 * q - 3) h0 h1]
  rw [hv]
  push_cast
  ring

lemma leftBraidFun_final_b {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    leftBraidFun n i j q (strandIdxSucc i) =
      twistPoint ((i : ℕ) + 3 / 2) (-1) (4 * q - 3) := by
  have hba : strandIdx i ≠ strandIdx j := braid_three_distinct_01 i j hji
  rw [leftBraidFun]
  simp only [if_neg hq1, if_neg hq2, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne hba (braid_three_distinct_02 i j hji)]
  rw [halfTwistFun_of_eq (4 * q - 3) (by simp [strandIdx])]

lemma leftBraidFun_final_c {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    leftBraidFun n i j q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 3 / 2) 1 (4 * q - 3) := by
  have hca : strandIdxSucc j ≠ strandIdx i := (braid_three_distinct_02 i j hji).symm
  have hcb : strandIdxSucc j ≠ strandIdxSucc i := by
    intro h
    have hv := congrArg Fin.val h
    simp [strandIdxSucc, hji] at hv
  rw [leftBraidFun]
  simp only [if_neg hq1, if_neg hq2]
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_right]
  rw [halfTwistFun_of_eq_succ (4 * q - 3) (by simp [strandIdx, hji]) (by simp [strandIdx, hji])]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      AdjacentLeftLocalFacts i j hji := by
  intro n i j hji
  exact {
    first_a := fun q hq => leftBraidFun_first_a i j q hq
    first_b := fun q hq => leftBraidFun_first_b i j q hq
    first_c := fun q hq => leftBraidFun_first_c i j hji q hq
    middle_a := fun q hq1 hq2 => leftBraidFun_middle_a i j hji q hq1 hq2
    middle_b := fun q hq1 hq2 => leftBraidFun_middle_b i j hji q hq1 hq2
    middle_c := fun q hq1 hq2 => leftBraidFun_middle_c i j hji q hq1 hq2
    final_a := fun q hq1 hq2 => leftBraidFun_final_a i j hji q hq1 hq2
    final_b := fun q hq1 hq2 => leftBraidFun_final_b i j hji q hq1 hq2
    final_c := fun q hq1 hq2 => leftBraidFun_final_c i j hji q hq1 hq2
  }
