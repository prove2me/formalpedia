-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_outer_reflection_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:19:40.043467+00:00
-- url     : https://prove2.me/submissions/dd3fdec3-1b9b-42b9-9dad-af7d9bc2874e

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma outer_reflect_a_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    outerRotateFun n i q (strandIdx i) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        outerRotateFun n i q (strandIdxSucc j)) := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [hO.outer_a q, hO.outer_c q]
  simp [twistPoint]
  ring

lemma outer_reflect_b_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    outerRotateFun n i q (strandIdxSucc i) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        outerRotateFun n i q (strandIdxSucc i)) := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [hO.outer_b q]
  push_cast
  ring

lemma outer_reflect_c_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    outerRotateFun n i q (strandIdxSucc j) =
      (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
        outerRotateFun n i q (strandIdx i)) := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [hO.outer_c q, hO.outer_a q]
  simp [twistPoint]
  ring

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : ℝ,
        outerRotateFun n i q (strandIdx i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            outerRotateFun n i q (strandIdxSucc j))) ∧
      (∀ q : ℝ,
        outerRotateFun n i q (strandIdxSucc i) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            outerRotateFun n i q (strandIdxSucc i))) ∧
      (∀ q : ℝ,
        outerRotateFun n i q (strandIdxSucc j) =
          (((2 * (((i : ℕ) : ℝ) + 2) : ℝ) : ℂ) -
            outerRotateFun n i q (strandIdx i))) := by
  intro n i j hji
  exact ⟨outer_reflect_a_v1 i j hji,
    ⟨outer_reflect_b_v1 i j hji, outer_reflect_c_v1 i j hji⟩⟩
