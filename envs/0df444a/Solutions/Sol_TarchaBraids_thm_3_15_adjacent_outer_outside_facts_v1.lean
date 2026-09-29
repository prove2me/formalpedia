-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_outer_outside_facts_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:40:18.195886+00:00
-- url     : https://prove2.me/submissions/9fc489e7-b4ae-465f-b82a-994c86800993

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_geometry_interfaces_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma outerRotateFun_a {n : ℕ} (i : Fin (n - 1)) (q : ℝ) :
    outerRotateFun n i q (strandIdx i) =
      twistPoint ((i : ℕ) + 2) (-2) q := by
  have h0 : (strandIdx i : ℕ) = (i : ℕ) := by simp [strandIdx]
  simp [outerRotateFun, h0]

lemma outerRotateFun_b {n : ℕ} (i : Fin (n - 1)) (q : ℝ) :
    outerRotateFun n i q (strandIdxSucc i) = ((((i : ℕ) : ℝ) + 2 : ℝ) : ℂ) := by
  have h0 : (strandIdxSucc i : ℕ) ≠ (i : ℕ) := by simp [strandIdxSucc]
  have h1 : (strandIdxSucc i : ℕ) = (i : ℕ) + 1 := by simp [strandIdxSucc]
  simp [outerRotateFun, h0, h1]

lemma outerRotateFun_c {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    outerRotateFun n i q (strandIdxSucc j) =
      twistPoint ((i : ℕ) + 2) 2 q := by
  have hv : (strandIdxSucc j : ℕ) = (i : ℕ) + 2 := by simp [strandIdxSucc, hji]
  have h0 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) := by omega
  have h1 : (strandIdxSucc j : ℕ) ≠ (i : ℕ) + 1 := by omega
  simp [outerRotateFun, h0, h1, hv]

lemma leftBraidFun_outside {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1) (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    leftBraidFun n i j q k = (((k : ℕ) + 1 : ℝ) : ℂ) := by
  have hki : k ≠ strandIdx i := by
    intro h
    exact h0 (by simpa [strandIdx] using congrArg Fin.val h)
  have hkis : k ≠ strandIdxSucc i := by
    intro h
    exact h1 (by simpa [strandIdxSucc] using congrArg Fin.val h)
  have hkj : k ≠ strandIdx j := by
    intro h
    apply h1
    simpa [strandIdx, hji] using congrArg Fin.val h
  have hkjs : k ≠ strandIdxSucc j := by
    intro h
    apply h2
    simpa [strandIdxSucc, hji] using congrArg Fin.val h
  have hkj0 : (k : ℕ) ≠ (j : ℕ) := by omega
  have hkj1 : (k : ℕ) ≠ (j : ℕ) + 1 := by omega
  by_cases hq1 : q ≤ 1 / 2
  · rw [leftBraidFun]
    simp only [if_pos hq1]
    exact halfTwistFun_of_fixed (2 * q) h0 h1
  · by_cases hq2 : q ≤ 3 / 4
    · rw [leftBraidFun]
      simp only [if_neg hq1, if_pos hq2]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkis]
      exact halfTwistFun_of_fixed (4 * q - 2) hkj0 hkj1
    · rw [leftBraidFun]
      simp only [if_neg hq1, if_neg hq2]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkis,
        Equiv.swap_apply_of_ne_of_ne hkj hkjs]
      exact halfTwistFun_of_fixed (4 * q - 3) h0 h1

lemma rightBraidFun_outside {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1) (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    rightBraidFun n i j q k = (((k : ℕ) + 1 : ℝ) : ℂ) := by
  have hki : k ≠ strandIdx i := by
    intro h
    exact h0 (by simpa [strandIdx] using congrArg Fin.val h)
  have hkis : k ≠ strandIdxSucc i := by
    intro h
    exact h1 (by simpa [strandIdxSucc] using congrArg Fin.val h)
  have hkj : k ≠ strandIdx j := by
    intro h
    apply h1
    simpa [strandIdx, hji] using congrArg Fin.val h
  have hkjs : k ≠ strandIdxSucc j := by
    intro h
    apply h2
    simpa [strandIdxSucc, hji] using congrArg Fin.val h
  have hkj0 : (k : ℕ) ≠ (j : ℕ) := by omega
  have hkj1 : (k : ℕ) ≠ (j : ℕ) + 1 := by omega
  by_cases hq1 : q ≤ 1 / 2
  · rw [rightBraidFun]
    simp only [if_pos hq1]
    exact halfTwistFun_of_fixed (2 * q) hkj0 hkj1
  · by_cases hq2 : q ≤ 3 / 4
    · rw [rightBraidFun]
      simp only [if_neg hq1, if_pos hq2]
      rw [Equiv.swap_apply_of_ne_of_ne hkj hkjs]
      exact halfTwistFun_of_fixed (4 * q - 2) h0 h1
    · rw [rightBraidFun]
      simp only [if_neg hq1, if_neg hq2]
      rw [Equiv.swap_apply_of_ne_of_ne hkj hkjs,
        Equiv.swap_apply_of_ne_of_ne hki hkis]
      exact halfTwistFun_of_fixed (4 * q - 3) hkj0 hkj1

lemma outerRotateFun_outside {n : ℕ} (i : Fin (n - 1)) (q : ℝ) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1) (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    outerRotateFun n i q k = (((k : ℕ) + 1 : ℝ) : ℂ) := by
  simp [outerRotateFun, h0, h1, h2]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      AdjacentOuterOutsideFacts i j hji := by
  intro n i j hji
  exact {
    outer_a := outerRotateFun_a i
    outer_b := outerRotateFun_b i
    outer_c := outerRotateFun_c i j hji
    left_outside := fun q k h0 h1 h2 => leftBraidFun_outside i j hji q k h0 h1 h2
    right_outside := fun q k h0 h1 h2 => rightBraidFun_outside i j hji q k h0 h1 h2
    outer_outside := fun q k h0 h1 h2 => outerRotateFun_outside i q k h0 h1 h2
  }
