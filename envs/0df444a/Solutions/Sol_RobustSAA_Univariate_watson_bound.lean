-- Prove2me | solution 1 for RobustSAA.Univariate.watson_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:52.821116+00:00
-- url     : https://prove2.me/submissions/c7291410-7080-44bf-bd37-7a6201b4b33c

import Definitions.Def_RobustSAA_Univariate_Setting
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open MeasureTheory Finset RobustSAA.Univariate
open scoped BigOperators

private lemma grid_sum (N : ℕ) :
    ∑ i : Fin N, (2 * ((i : ℕ) + 1 : ℝ) - 1) = (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem solution {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    cvmStat F₀ s ^ 2 - watsonStat F₀ s ^ 2 = meanDev F₀ s ^ 2 ∧
    meanDev F₀ s ^ 2 ≤
      max ((1 / (N : ℝ) * ∑ i : Fin N,
              min 1 ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) + Dprime F₀ s) - 1 / 2) ^ 2)
          ((1 / (N : ℝ) * ∑ i : Fin N,
              max 0 ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - Dprime F₀ s) - 1 / 2) ^ 2) := by
  classical
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNz : (N : ℝ) ≠ 0 := ne_of_gt hNr
  let a : Fin N → ℝ := fun i => (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N)
  let v : Fin N → ℝ := fun i => a i - u F₀ s i
  have ha : ∑ i, a i = (N : ℝ) / 2 := by
    dsimp [a]
    rw [← sum_div, grid_sum]
    field_simp
    <;> ring
  have hv : ∑ i, v i = -(N : ℝ) * meanDev F₀ s := by
    dsimp [v]
    rw [sum_sub_distrib, ha]
    dsimp [meanDev]
    field_simp
    <;> ring
  have hcs := sum_mul_sq_le_sq_mul_sq univ v (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, hv] at hcs
  have hvar : meanDev F₀ s ^ 2 ≤ (1 / (N : ℝ)) * ∑ i, v i ^ 2 := by
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hNr).mpr
    have hh : (N : ℝ) * meanDev F₀ s ^ 2 ≤ ∑ i, v i ^ 2 := by
      apply (mul_le_mul_iff_right₀ hNr).mp
      nlinarith [hcs]
    nlinarith [hh]
  have hcvm : cvmStat F₀ s ^ 2 = 1 / (12 * (N : ℝ) ^ 2) +
      (1 / (N : ℝ)) * ∑ i, v i ^ 2 := by
    dsimp [cvmStat, v, a]
    exact Real.sq_sqrt (by positivity)
  have hw : 0 ≤ cvmStat F₀ s ^ 2 - meanDev F₀ s ^ 2 := by
    rw [hcvm]
    have hconst : 0 ≤ 1 / (12 * (N : ℝ) ^ 2) := by positivity
    linarith
  constructor
  · rw [watsonStat, Real.sq_sqrt hw]
    ring
  let hi : ℝ := 1 / (N : ℝ) * ∑ i, min 1 (a i + Dprime F₀ s) - 1 / 2
  let lo : ℝ := 1 / (N : ℝ) * ∑ i, max 0 (a i - Dprime F₀ s) - 1 / 2
  have hpoint (i : Fin N) : |u F₀ s i - a i| ≤ Dprime F₀ s := by
    dsimp [Dprime, a]
    exact le_ciSup (Set.finite_range (fun j : Fin N => |u F₀ s j - (2 * ((j : ℕ) + 1 : ℝ) - 1) / (2 * N)|)).bddAbove i
  have hu0 (i : Fin N) : 0 ≤ u F₀ s i := ProbabilityTheory.cdf_nonneg _ _
  have hu1 (i : Fin N) : u F₀ s i ≤ 1 := ProbabilityTheory.cdf_le_one _ _
  have hlo : lo ≤ meanDev F₀ s := by
    dsimp [lo, meanDev]
    apply sub_le_sub_right
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro i _
    exact max_le (hu0 i) (by linarith [(abs_le.mp (hpoint i)).1])
  have hhi : meanDev F₀ s ≤ hi := by
    dsimp [hi, meanDev]
    apply sub_le_sub_right
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro i _
    exact le_min (hu1 i) (by linarith [(abs_le.mp (hpoint i)).2])
  change meanDev F₀ s ^ 2 ≤ max (hi ^ 2) (lo ^ 2)
  by_cases hm : 0 ≤ meanDev F₀ s
  · exact (sq_le_sq₀ hm (hm.trans hhi) |>.mpr hhi).trans (le_max_left _ _)
  · have hm' : meanDev F₀ s ≤ 0 := le_of_not_ge hm
    have hs := sq_le_sq₀ (neg_nonneg.mpr hm') (neg_nonneg.mpr (hlo.trans hm'))
    have hsq : meanDev F₀ s ^ 2 ≤ lo ^ 2 := by
      simpa only [neg_sq] using hs.mpr (neg_le_neg hlo)
    exact hsq.trans (le_max_right _ _)

#print axioms solution


