-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_first_local_facts_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:13:02.512306+00:00
-- url     : https://prove2.me/submissions/2c1f6138-0c33-4a5a-be95-7a150d0f23b7

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma right_first_a_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) (hq : q ≤ 1 / 2) :
    rightBraidFun n i j q (strandIdx i) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by
  have hv : (strandIdx i : ℕ) = (i : ℕ) := by
    simp [strandIdx]
  have h0 : (strandIdx i : ℕ) ≠ (j : ℕ) := by
    omega
  have h1 : (strandIdx i : ℕ) ≠ (j : ℕ) + 1 := by
    omega
  rw [rightBraidFun]
  simp only [if_pos hq]
  rw [halfTwistFun_of_fixed (2 * q) h0 h1]
  rw [hv]

lemma right_first_b_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) (hq : q ≤ 1 / 2) :
    rightBraidFun n i j q (strandIdxSucc i) =
      twistPoint ((i : ℕ) + 5 / 2) (-1) (2 * q) := by
  rw [rightBraidFun]
  simp only [if_pos hq]
  rw [halfTwistFun_of_eq (2 * q) (by simp [strandIdxSucc, hji])]
  have hc : ((j : ℕ) : ℝ) + 3 / 2 = ((i : ℕ) : ℝ) + 5 / 2 := by
    rw [hji]
    push_cast
    ring
  rw [hc]

lemma right_first_c_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) (hq : q ≤ 1 / 2) :
    rightBraidFun n i j q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 5 / 2) 1 (2 * q) := by
  rw [rightBraidFun]
  simp only [if_pos hq]
  rw [halfTwistFun_of_eq_succ (2 * q)
    (by simp [strandIdxSucc]) (by simp [strandIdxSucc])]
  have hc : ((j : ℕ) : ℝ) + 3 / 2 = ((i : ℕ) : ℝ) + 5 / 2 := by
    rw [hji]
    push_cast
    ring
  rw [hc]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (q : ℝ), q ≤ 1 / 2 →
        rightBraidFun n i j q (strandIdx i) = ((((i : ℕ) : ℝ) + 1 : ℝ) : ℂ)) ∧
      (∀ (q : ℝ), q ≤ 1 / 2 →
        rightBraidFun n i j q (strandIdxSucc i) =
          twistPoint ((i : ℕ) + 5 / 2) (-1) (2 * q)) ∧
      (∀ (q : ℝ), q ≤ 1 / 2 →
        rightBraidFun n i j q (strandIdxSucc j) =
          twistPoint ((i : ℕ) + 5 / 2) 1 (2 * q)) := by
  intro n i j hji
  exact ⟨
    fun q hq => right_first_a_v1 i j hji q hq,
    ⟨fun q hq => right_first_b_v1 i j hji q hq,
      fun q hq => right_first_c_v1 i j hji q hq⟩
  ⟩
