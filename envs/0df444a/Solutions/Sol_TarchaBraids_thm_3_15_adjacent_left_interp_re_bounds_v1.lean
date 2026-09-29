-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_left_interp_re_bounds_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T09:46:18.903114+00:00
-- url     : https://prove2.me/submissions/108dd289-90b3-499a-887f-bca41a57c11d

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_separation_interfaces_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1

namespace TarchaBraids

open BraidsLinksMCG

@[simp] lemma braidInterp_re_bounds_v1 (u : ℝ) (z w : ℂ) :
    (braidInterp u z w).re = (1 - u) * z.re + u * w.re := by
  simp [braidInterp]

lemma braidInterp_re_mem_interval_bounds_v1 {u c z w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hz0 : c - 1 ≤ z) (hz1 : z ≤ c + 1)
    (hw0 : c - 1 ≤ w) (hw1 : w ≤ c + 1) :
    c - 1 ≤ (1 - u) * z + u * w ∧
      (1 - u) * z + u * w ≤ c + 1 := by
  have h1u : 0 ≤ 1 - u := by linarith
  have hlo1 : 0 ≤ (1 - u) * (z - (c - 1)) :=
    mul_nonneg h1u (sub_nonneg.mpr hz0)
  have hlo2 : 0 ≤ u * (w - (c - 1)) :=
    mul_nonneg hu0 (sub_nonneg.mpr hw0)
  have hhi1 : 0 ≤ (1 - u) * ((c + 1) - z) :=
    mul_nonneg h1u (sub_nonneg.mpr hz1)
  have hhi2 : 0 ≤ u * ((c + 1) - w) :=
    mul_nonneg hu0 (sub_nonneg.mpr hw1)
  constructor <;> nlinarith

lemma leftBraidFun_a_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    ((i : ℕ) : ℝ) + 1 ≤ (leftBraidFun n i j q (strandIdx i)).re ∧
      (leftBraidFun n i j q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  by_cases hq1 : q ≤ 1 / 2
  · rw [hL.first_a q hq1]
    simp only [twistPoint_re]
    have hcl := Real.neg_one_le_cos (Real.pi * (2 * q))
    have hcu := Real.cos_le_one (Real.pi * (2 * q))
    constructor <;> linarith
  · by_cases hq2 : q ≤ 3 / 4
    · rw [hL.middle_a q hq1 hq2]
      simp only [twistPoint_re]
      have hcl := Real.neg_one_le_cos (Real.pi * (4 * q - 2))
      have hcu := Real.cos_le_one (Real.pi * (4 * q - 2))
      constructor <;> linarith
    · rw [hL.final_a q hq1 hq2]
      simp

lemma leftBraidFun_b_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    ((i : ℕ) : ℝ) + 1 ≤ (leftBraidFun n i j q (strandIdxSucc i)).re ∧
      (leftBraidFun n i j q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  by_cases hq1 : q ≤ 1 / 2
  · rw [hL.first_b q hq1]
    simp only [twistPoint_re]
    have hcl := Real.neg_one_le_cos (Real.pi * (2 * q))
    have hcu := Real.cos_le_one (Real.pi * (2 * q))
    constructor <;> linarith
  · by_cases hq2 : q ≤ 3 / 4
    · rw [hL.middle_b q hq1 hq2]
      simp
    · rw [hL.final_b q hq1 hq2]
      simp only [twistPoint_re]
      have hcl := Real.neg_one_le_cos (Real.pi * (4 * q - 3))
      have hcu := Real.cos_le_one (Real.pi * (4 * q - 3))
      constructor <;> linarith

lemma leftBraidFun_c_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    ((i : ℕ) : ℝ) + 1 ≤ (leftBraidFun n i j q (strandIdxSucc j)).re ∧
      (leftBraidFun n i j q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  by_cases hq1 : q ≤ 1 / 2
  · rw [hL.first_c q hq1]
    simp
  · by_cases hq2 : q ≤ 3 / 4
    · rw [hL.middle_c q hq1 hq2]
      simp only [twistPoint_re]
      have hcl := Real.neg_one_le_cos (Real.pi * (4 * q - 2))
      have hcu := Real.cos_le_one (Real.pi * (4 * q - 2))
      constructor <;> linarith
    · rw [hL.final_c q hq1 hq2]
      simp only [twistPoint_re]
      have hcl := Real.neg_one_le_cos (Real.pi * (4 * q - 3))
      have hcu := Real.cos_le_one (Real.pi * (4 * q - 3))
      constructor <;> linarith

lemma outerRotateFun_a_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    ((i : ℕ) : ℝ) + 1 ≤ (outerRotateFun n i q (strandIdx i)).re ∧
      (outerRotateFun n i q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [hO.outer_a q]
  simp only [twistPoint_re]
  have hcl := Real.neg_one_le_cos (Real.pi * q)
  have hcu := Real.cos_le_one (Real.pi * q)
  constructor <;> linarith

lemma outerRotateFun_b_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    ((i : ℕ) : ℝ) + 1 ≤ (outerRotateFun n i q (strandIdxSucc i)).re ∧
      (outerRotateFun n i q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [hO.outer_b q]
  simp only [Complex.ofReal_re]
  constructor <;> linarith

lemma outerRotateFun_c_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : ℝ) :
    ((i : ℕ) : ℝ) + 1 ≤ (outerRotateFun n i q (strandIdxSucc j)).re ∧
      (outerRotateFun n i q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [hO.outer_c q]
  simp only [twistPoint_re]
  have hcl := Real.neg_one_le_cos (Real.pi * q)
  have hcu := Real.cos_le_one (Real.pi * q)
  constructor <;> linarith

lemma leftInterp_a_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdx i)).re ∧
      (leftOuterInterpFun n i j u q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  rw [leftOuterInterpFun, braidInterp_re_bounds_v1]
  have hL := leftBraidFun_a_re_bounds_v1 i j hji q
  have hR := outerRotateFun_a_re_bounds_v1 i j hji q
  have h := braidInterp_re_mem_interval_bounds_v1
    (u := u) (c := ((i : ℕ) : ℝ) + 2)
    hu0 hu1 (by linarith [hL.1]) (by linarith [hL.2])
    (by linarith [hR.1]) (by linarith [hR.2])
  constructor <;> nlinarith [h.1, h.2]

lemma leftInterp_b_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ∧
      (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  rw [leftOuterInterpFun, braidInterp_re_bounds_v1]
  have hL := leftBraidFun_b_re_bounds_v1 i j hji q
  have hR := outerRotateFun_b_re_bounds_v1 i j hji q
  have h := braidInterp_re_mem_interval_bounds_v1
    (u := u) (c := ((i : ℕ) : ℝ) + 2)
    hu0 hu1 (by linarith [hL.1]) (by linarith [hL.2])
    (by linarith [hR.1]) (by linarith [hR.2])
  constructor <;> nlinarith [h.1, h.2]

lemma leftInterp_c_re_bounds_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc j)).re ∧
      (leftOuterInterpFun n i j u q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3 := by
  rw [leftOuterInterpFun, braidInterp_re_bounds_v1]
  have hL := leftBraidFun_c_re_bounds_v1 i j hji q
  have hR := outerRotateFun_c_re_bounds_v1 i j hji q
  have h := braidInterp_re_mem_interval_bounds_v1
    (u := u) (c := ((i : ℕ) : ℝ) + 2)
    hu0 hu1 (by linarith [hL.1]) (by linarith [hL.2])
    (by linarith [hR.1]) (by linarith [hR.2])
  constructor <;> nlinarith [h.1, h.2]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdx i)).re ∧
        (leftOuterInterpFun n i j u q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ∧
        (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 3) ∧
      (∀ (u q : ℝ), 0 ≤ u → u ≤ 1 →
        ((i : ℕ) : ℝ) + 1 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc j)).re ∧
        (leftOuterInterpFun n i j u q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 3) := by
  intro n i j hji
  exact ⟨
    fun u q hu0 hu1 => leftInterp_a_re_bounds_v1 i j hji u q hu0 hu1,
    ⟨fun u q hu0 hu1 => leftInterp_b_re_bounds_v1 i j hji u q hu0 hu1,
      fun u q hu0 hu1 => leftInterp_c_re_bounds_v1 i j hji u q hu0 hu1⟩
  ⟩
