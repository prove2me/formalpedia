-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_pairwise_separation_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T10:58:48.925054+00:00
-- url     : https://prove2.me/submissions/ea7b4723-c0b2-499b-9447-925216fbd31b

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_pairwise_separation_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_reflection_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightInterp_local01_ne_reflect_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    rightOuterInterpFun n i j u q (strandIdx i) ≠
      rightOuterInterpFun n i j u q (strandIdxSucc i) := by
  have hR := thm_3_15_adjacent_right_interp_reflection_v1 i j hji
  have hL := thm_3_15_adjacent_left_pairwise_separation_v1 i j hji
  intro h
  rw [hR.1 u q, hR.2.1 u q] at h
  have hcb :
      leftOuterInterpFun n i j u q (strandIdxSucc j) =
        leftOuterInterpFun n i j u q (strandIdxSucc i) :=
    sub_right_inj.mp h
  exact (hL.local12_ne u q hu0 hu1 hq0 hq1) hcb.symm

lemma rightInterp_local02_ne_reflect_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    rightOuterInterpFun n i j u q (strandIdx i) ≠
      rightOuterInterpFun n i j u q (strandIdxSucc j) := by
  have hR := thm_3_15_adjacent_right_interp_reflection_v1 i j hji
  have hL := thm_3_15_adjacent_left_pairwise_separation_v1 i j hji
  intro h
  rw [hR.1 u q, hR.2.2 u q] at h
  have hca :
      leftOuterInterpFun n i j u q (strandIdxSucc j) =
        leftOuterInterpFun n i j u q (strandIdx i) :=
    sub_right_inj.mp h
  exact (hL.local02_ne u q hu0 hu1 hq0 hq1) hca.symm

lemma rightInterp_local12_ne_reflect_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    rightOuterInterpFun n i j u q (strandIdxSucc i) ≠
      rightOuterInterpFun n i j u q (strandIdxSucc j) := by
  have hR := thm_3_15_adjacent_right_interp_reflection_v1 i j hji
  have hL := thm_3_15_adjacent_left_pairwise_separation_v1 i j hji
  intro h
  rw [hR.2.1 u q, hR.2.2 u q] at h
  have hba :
      leftOuterInterpFun n i j u q (strandIdxSucc i) =
        leftOuterInterpFun n i j u q (strandIdx i) :=
    sub_right_inj.mp h
  exact (hL.local01_ne u q hu0 hu1 hq0 hq1) hba.symm

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
        rightOuterInterpFun n i j u q (strandIdx i) ≠
          rightOuterInterpFun n i j u q (strandIdxSucc i)) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
        rightOuterInterpFun n i j u q (strandIdx i) ≠
          rightOuterInterpFun n i j u q (strandIdxSucc j)) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
        rightOuterInterpFun n i j u q (strandIdxSucc i) ≠
          rightOuterInterpFun n i j u q (strandIdxSucc j)) := by
  intro n i j hji
  exact ⟨
    fun u q hu0 hu1 hq0 hq1 =>
      rightInterp_local01_ne_reflect_v1 i j hji u q hu0 hu1 hq0 hq1,
    ⟨fun u q hu0 hu1 hq0 hq1 =>
      rightInterp_local02_ne_reflect_v1 i j hji u q hu0 hu1 hq0 hq1,
      fun u q hu0 hu1 hq0 hq1 =>
        rightInterp_local12_ne_reflect_v1 i j hji u q hu0 hu1 hq0 hq1⟩
  ⟩
