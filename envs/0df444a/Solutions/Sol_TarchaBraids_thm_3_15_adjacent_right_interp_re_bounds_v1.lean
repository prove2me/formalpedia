-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_interp_re_bounds_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:53:40.624465+00:00
-- url     : https://prove2.me/submissions/b3948445-f4ce-4d4f-8343-922a6296ea3b

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_interp_re_bounds_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_reflection_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma reflected_re_bounds_v1 {c : ℝ} {x y : ℂ}
    (hxy : x = ((2 * c : ℝ) : ℂ) - y)
    (hy0 : c - 1 ≤ y.re) (hy1 : y.re ≤ c + 1) :
    c - 1 ≤ x.re ∧ x.re ≤ c + 1 := by
  have hre := congrArg Complex.re hxy
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  constructor <;> linarith

lemma rightInterp_a_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdx i)).re ∧
      (rightOuterInterpFun n i j u q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hR := thm_3_15_adjacent_right_interp_reflection_v1 i j hji
  have hL := thm_3_15_adjacent_left_interp_re_bounds_v1 i j hji
  have hB := hL.2.2 u q hu0 hu1
  have h := reflected_re_bounds_v1
    (c := ((i : ℕ) : ℝ) + 2)
    (hxy := hR.1 u q)
    (hy0 := by linarith [hB.1])
    (hy1 := by linarith [hB.2])
  constructor <;> linarith [h.1, h.2]

lemma rightInterp_b_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdxSucc i)).re ∧
      (rightOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hR := thm_3_15_adjacent_right_interp_reflection_v1 i j hji
  have hL := thm_3_15_adjacent_left_interp_re_bounds_v1 i j hji
  have hB := hL.2.1 u q hu0 hu1
  have h := reflected_re_bounds_v1
    (c := ((i : ℕ) : ℝ) + 2)
    (hxy := hR.2.1 u q)
    (hy0 := by linarith [hB.1])
    (hy1 := by linarith [hB.2])
  constructor <;> linarith [h.1, h.2]

lemma rightInterp_c_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdxSucc j)).re ∧
      (rightOuterInterpFun n i j u q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hR := thm_3_15_adjacent_right_interp_reflection_v1 i j hji
  have hL := thm_3_15_adjacent_left_interp_re_bounds_v1 i j hji
  have hB := hL.1 u q hu0 hu1
  have h := reflected_re_bounds_v1
    (c := ((i : ℕ) : ℝ) + 2)
    (hxy := hR.2.2 u q)
    (hy0 := by linarith [hB.1])
    (hy1 := by linarith [hB.2])
  constructor <;> linarith [h.1, h.2]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdx i)).re ∧
        (rightOuterInterpFun n i j u q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdxSucc i)).re ∧
        (rightOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (rightOuterInterpFun n i j u q (strandIdxSucc j)).re ∧
        (rightOuterInterpFun n i j u q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3) := by
  intro n i j hji
  exact ⟨
    fun u q hu0 hu1 => rightInterp_a_re_bounds_v1 i j hji u q hu0 hu1,
    ⟨fun u q hu0 hu1 => rightInterp_b_re_bounds_v1 i j hji u q hu0 hu1,
      fun u q hu0 hu1 => rightInterp_c_re_bounds_v1 i j hji u q hu0 hu1⟩
  ⟩
