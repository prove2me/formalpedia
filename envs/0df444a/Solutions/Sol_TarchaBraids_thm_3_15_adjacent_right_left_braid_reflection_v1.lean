-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_left_braid_reflection_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:21:50.428256+00:00
-- url     : https://prove2.me/submissions/3c03fc5a-ce66-416a-a8e8-7b6071d924d8

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_first_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_middle_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_final_local_facts_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma right_left_reflect_a_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    rightBraidFun n i j q (strandIdx i) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        leftBraidFun n i j q (strandIdxSucc j)) := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hR1 := thm_3_15_adjacent_right_first_local_facts_v1 i j hji
  have hRM := thm_3_15_adjacent_right_middle_local_facts_v1 i j hji
  have hRF := thm_3_15_adjacent_right_final_local_facts_v1 i j hji
  by_cases hq1 : q ≤ 1 / 2
  · rw [hR1.1 q hq1, hL.first_c q hq1]
    push_cast
    ring
  · by_cases hq2 : q ≤ 3 / 4
    · rw [hRM.1 q hq1 hq2, hL.middle_c q hq1 hq2]
      simp [twistPoint]
      ring
    · rw [hRF.1 q hq1 hq2, hL.final_c q hq1 hq2]
      simp [twistPoint]
      ring

lemma right_left_reflect_b_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    rightBraidFun n i j q (strandIdxSucc i) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        leftBraidFun n i j q (strandIdxSucc i)) := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hR1 := thm_3_15_adjacent_right_first_local_facts_v1 i j hji
  have hRM := thm_3_15_adjacent_right_middle_local_facts_v1 i j hji
  have hRF := thm_3_15_adjacent_right_final_local_facts_v1 i j hji
  by_cases hq1 : q ≤ 1 / 2
  · rw [hR1.2.1 q hq1, hL.first_b q hq1]
    simp [twistPoint]
    ring
  · by_cases hq2 : q ≤ 3 / 4
    · rw [hRM.2.1 q hq1 hq2, hL.middle_b q hq1 hq2]
      push_cast
      ring
    · rw [hRF.2.1 q hq1 hq2, hL.final_b q hq1 hq2]
      simp [twistPoint]
      ring

lemma right_left_reflect_c_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    rightBraidFun n i j q (strandIdxSucc j) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        leftBraidFun n i j q (strandIdx i)) := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hR1 := thm_3_15_adjacent_right_first_local_facts_v1 i j hji
  have hRM := thm_3_15_adjacent_right_middle_local_facts_v1 i j hji
  have hRF := thm_3_15_adjacent_right_final_local_facts_v1 i j hji
  by_cases hq1 : q ≤ 1 / 2
  · rw [hR1.2.2 q hq1, hL.first_a q hq1]
    simp [twistPoint]
    ring
  · by_cases hq2 : q ≤ 3 / 4
    · rw [hRM.2.2 q hq1 hq2, hL.middle_a q hq1 hq2]
      simp [twistPoint]
      ring
    · rw [hRF.2.2 q hq1 hq2, hL.final_a q hq1 hq2]
      push_cast
      ring

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : ℝ,
        rightBraidFun n i j q (strandIdx i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftBraidFun n i j q (strandIdxSucc j))) ∧
      (∀ q : ℝ,
        rightBraidFun n i j q (strandIdxSucc i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftBraidFun n i j q (strandIdxSucc i))) ∧
      (∀ q : ℝ,
        rightBraidFun n i j q (strandIdxSucc j) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            leftBraidFun n i j q (strandIdx i))) := by
  intro n i j hji
  exact ⟨right_left_reflect_a_v1 i j hji,
    ⟨right_left_reflect_b_v1 i j hji, right_left_reflect_c_v1 i j hji⟩⟩
