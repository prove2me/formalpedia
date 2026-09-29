-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_outside_separation_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:58:33.920557+00:00
-- url     : https://prove2.me/submissions/ea28ee7f-e93e-4928-b961-dc546220d59b

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_re_bounds_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightOuterInterpFun_outside_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1)
    (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    rightOuterInterpFun n i j u q k = (((k : ℕ) + 1 : ℝ) : ℂ) := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [rightOuterInterpFun, hO.right_outside q k h0 h1 h2,
    hO.outer_outside q k h0 h1 h2]
  unfold braidInterp
  module

lemma complex_ne_base_outside_right_v1 {i k : ℕ} {z : ℂ}
    (hz0 : (i : ℝ) + 1 ≤ z.re) (hz1 : z.re ≤ (i : ℝ) + 3)
    (h0 : k ≠ i) (h1 : k ≠ i + 1) (h2 : k ≠ i + 2) :
    z ≠ (((k : ℕ) + 1 : ℝ) : ℂ) := by
  intro h
  have hre : z.re = (k : ℝ) + 1 := by
    simpa using congrArg Complex.re h
  have hcase : k < i ∨ i + 2 < k := by omega
  rcases hcase with hki | hik
  · have hkR : (k : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast (by omega : k + 1 ≤ i)
    linarith
  · have hkR : (i : ℝ) + 4 ≤ (k : ℝ) + 1 := by
      exact_mod_cast (by omega : i + 4 ≤ k + 1)
    linarith

lemma rightInterp_a_ne_outside_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1)
    (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    rightOuterInterpFun n i j u q (strandIdx i) ≠
      rightOuterInterpFun n i j u q k := by
  rw [rightOuterInterpFun_outside_v1 i j hji u q k h0 h1 h2]
  have hB := thm_3_15_adjacent_right_interp_re_bounds_v1 i j hji
  have hb := hB.1 u q hu0 hu1
  exact complex_ne_base_outside_right_v1 hb.1 hb.2 h0 h1 h2

lemma rightInterp_b_ne_outside_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1)
    (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    rightOuterInterpFun n i j u q (strandIdxSucc i) ≠
      rightOuterInterpFun n i j u q k := by
  rw [rightOuterInterpFun_outside_v1 i j hji u q k h0 h1 h2]
  have hB := thm_3_15_adjacent_right_interp_re_bounds_v1 i j hji
  have hb := hB.2.1 u q hu0 hu1
  exact complex_ne_base_outside_right_v1 hb.1 hb.2 h0 h1 h2

lemma rightInterp_c_ne_outside_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1)
    (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    rightOuterInterpFun n i j u q (strandIdxSucc j) ≠
      rightOuterInterpFun n i j u q k := by
  rw [rightOuterInterpFun_outside_v1 i j hji u q k h0 h1 h2]
  have hB := thm_3_15_adjacent_right_interp_re_bounds_v1 i j hji
  have hb := hB.2.2 u q hu0 hu1
  exact complex_ne_base_outside_right_v1 hb.1 hb.2 h0 h1 h2

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ∀ (k : Fin n),
          (k : ℕ) ≠ (i : ℕ) →
          (k : ℕ) ≠ (i : ℕ) + 1 →
          (k : ℕ) ≠ (i : ℕ) + 2 →
          rightOuterInterpFun n i j u q (strandIdx i) ≠
            rightOuterInterpFun n i j u q k) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ∀ (k : Fin n),
          (k : ℕ) ≠ (i : ℕ) →
          (k : ℕ) ≠ (i : ℕ) + 1 →
          (k : ℕ) ≠ (i : ℕ) + 2 →
          rightOuterInterpFun n i j u q (strandIdxSucc i) ≠
            rightOuterInterpFun n i j u q k) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ∀ (k : Fin n),
          (k : ℕ) ≠ (i : ℕ) →
          (k : ℕ) ≠ (i : ℕ) + 1 →
          (k : ℕ) ≠ (i : ℕ) + 2 →
          rightOuterInterpFun n i j u q (strandIdxSucc j) ≠
            rightOuterInterpFun n i j u q k) := by
  intro n i j hji
  exact ⟨
    fun u q hu0 hu1 k h0 h1 h2 =>
      rightInterp_a_ne_outside_v1 i j hji u q hu0 hu1 k h0 h1 h2,
    ⟨fun u q hu0 hu1 k h0 h1 h2 =>
      rightInterp_b_ne_outside_v1 i j hji u q hu0 hu1 k h0 h1 h2,
      fun u q hu0 hu1 k h0 h1 h2 =>
        rightInterp_c_ne_outside_v1 i j hji u q hu0 hu1 k h0 h1 h2⟩
  ⟩
