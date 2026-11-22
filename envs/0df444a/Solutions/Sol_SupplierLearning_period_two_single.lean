-- Prove2me | solution 1 for SupplierLearning.period_two_single
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:40:12.714642+00:00
-- url     : https://prove2.me/submissions/e7b47e2f-066e-4dc0-9a66-9226a32770b8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_separatingHigh
import Definitions.Def_SupplierLearning_Params_separatingLow
import Definitions.Def_SupplierLearning_Params_poolingQuantity
import Definitions.Def_SupplierLearning_Params_IsPeriodTwoMax

set_option autoImplicit false

open SupplierLearning

theorem solution (P : Params) (hP : P.Standing) {q : ℝ}
    (hk : P.ch - P.rh * q ≤ P.cl) :
    (P.separatingLow q < P.separatingHigh q →
      P.IsPeriodTwoMax q (P.separatingHigh q) (P.separatingLow q)) ∧
    (P.separatingHigh q ≤ P.separatingLow q →
      P.IsPeriodTwoMax q (P.poolingQuantity q) (P.poolingQuantity q)) ∧
    (P.separatingLow q < P.separatingHigh q ↔ P.ν * P.rl < P.rh) := by
  have hδ := hP.δ_pos
  have hρ0 := hP.ρ_pos
  have hρ1 := hP.ρ_lt_one
  have hν0 := hP.ν_pos
  have hν1 := hP.ν_lt_one
  have hrh := hP.rh_pos
  have hcl := hP.cost_lt
  have hq : 0 < q := by
    have : 0 < P.rh * q := by linarith
    exact (mul_pos_iff_of_pos_left hrh).mp this
  have hw1 : 0 < P.δ * P.ρ := mul_pos hδ hρ0
  have hw2 : 0 < P.δ * (1 - P.ρ) := mul_pos hδ (by linarith)
  have hY : P.separatingHigh q = (P.a₂ - P.ch + P.rh * q) / 2 - 1 / 2 * P.kappa * P.deltaC -
      1 / 2 * P.kappa * q * P.deltaR := by
    rw [Params.separatingHigh, if_pos hk]
  have hZ : P.separatingLow q = (P.a₂ - P.ch) / 2 - 1 / 2 * P.kappa * P.deltaC := by
    rw [Params.separatingLow, if_pos hk]
  have hR : ∀ y z, z ≤ y → P.reducedObjective q y z =
      P.typeSurplus .h q y z - P.kappa * P.rentFloor q y z := by
    intro y z hzy
    have hm : max 0 ((P.deltaC - P.rh * q) * (y - z)) = 0 := by
      apply max_eq_left
      have h1 : P.deltaC - P.rh * q ≤ 0 := by unfold Params.deltaC; linarith
      nlinarith
    rw [Params.reducedObjective, Params.rentBound, hm]
    ring
  have hsq : ∀ y z y2 z2, (P.typeSurplus .h q y z - P.kappa * P.rentFloor q y z) -
      (P.typeSurplus .h q y2 z2 - P.kappa * P.rentFloor q y2 z2) =
      -(P.δ * P.ρ) * ((y - P.separatingHigh q) ^ 2 - (y2 - P.separatingHigh q) ^ 2) -
        P.δ * (1 - P.ρ) * ((z - P.separatingLow q) ^ 2 - (z2 - P.separatingLow q) ^ 2) := by
    intro y z y2 z2
    rw [hY, hZ]
    simp only [Params.typeSurplus, Params.rentFloor, Params.cost, Params.rate]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro hZY
    refine ⟨hZY.le, fun y' z' hz' => ?_⟩
    rw [hR y' z' hz', hR _ _ hZY.le]
    have h := hsq y' z' (P.separatingHigh q) (P.separatingLow q)
    have hA := mul_nonneg hw1.le (sq_nonneg (y' - P.separatingHigh q))
    have hB := mul_nonneg hw2.le (sq_nonneg (z' - P.separatingLow q))
    have hd : P.typeSurplus .h q y' z' - P.kappa * P.rentFloor q y' z' -
        (P.typeSurplus .h q (P.separatingHigh q) (P.separatingLow q) -
          P.kappa * P.rentFloor q (P.separatingHigh q) (P.separatingLow q)) =
        -(P.δ * P.ρ * (y' - P.separatingHigh q) ^ 2 +
          P.δ * (1 - P.ρ) * (z' - P.separatingLow q) ^ 2) := by
      rw [h]
      ring
    constructor
    · have : -(P.δ * P.ρ * (y' - P.separatingHigh q) ^ 2 +
          P.δ * (1 - P.ρ) * (z' - P.separatingLow q) ^ 2) ≤ 0 := by
        rw [neg_nonpos]
        exact add_nonneg hA hB
      linarith
    · intro heq
      have hsum : P.δ * P.ρ * (y' - P.separatingHigh q) ^ 2 +
          P.δ * (1 - P.ρ) * (z' - P.separatingLow q) ^ 2 = 0 := by
        have : -(P.δ * P.ρ * (y' - P.separatingHigh q) ^ 2 +
          P.δ * (1 - P.ρ) * (z' - P.separatingLow q) ^ 2) = 0 := by rw [← hd]; linarith
        linarith
      have h2 : P.δ * P.ρ * (y' - P.separatingHigh q) ^ 2 = 0 := by linarith
      have h3 : P.δ * (1 - P.ρ) * (z' - P.separatingLow q) ^ 2 = 0 := by linarith
      have e2 := (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h2).resolve_left hw1.ne')
      have e3 := (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h3).resolve_left hw2.ne')
      constructor <;> linarith
  · intro hYZ
    have hT : P.poolingQuantity q = P.ρ * P.separatingHigh q + (1 - P.ρ) * P.separatingLow q := by
      rw [Params.poolingQuantity, hY, hZ]
      ring
    refine ⟨le_rfl, fun y' z' hz' => ?_⟩
    rw [hR y' z' hz', hR _ _ le_rfl]
    have h := hsq y' z' (P.poolingQuantity q) (P.poolingQuantity q)
    have expand : -(P.δ * P.ρ) * ((y' - P.separatingHigh q) ^ 2 -
          (P.poolingQuantity q - P.separatingHigh q) ^ 2) -
        P.δ * (1 - P.ρ) * ((z' - P.separatingLow q) ^ 2 -
          (P.poolingQuantity q - P.separatingLow q) ^ 2) =
        -P.δ * (P.ρ * (y' - P.poolingQuantity q) ^ 2 + (1 - P.ρ) * (z' - P.poolingQuantity q) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (P.separatingLow q - P.separatingHigh q) * (y' - z')) := by
      rw [hT]
      ring
    have hA := mul_nonneg hρ0.le (sq_nonneg (y' - P.poolingQuantity q))
    have hB := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - P.ρ) (sq_nonneg (z' - P.poolingQuantity q))
    have hC : 0 ≤ 2 * P.ρ * (1 - P.ρ) * (P.separatingLow q - P.separatingHigh q) * (y' - z') := by
      apply mul_nonneg
      apply mul_nonneg
      · nlinarith
      · linarith
      · linarith
    have hS : 0 ≤ P.ρ * (y' - P.poolingQuantity q) ^ 2 + (1 - P.ρ) * (z' - P.poolingQuantity q) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (P.separatingLow q - P.separatingHigh q) * (y' - z') := by linarith
    rw [expand, neg_mul] at h
    constructor
    · have : -(P.δ * (P.ρ * (y' - P.poolingQuantity q) ^ 2 +
          (1 - P.ρ) * (z' - P.poolingQuantity q) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (P.separatingLow q - P.separatingHigh q) * (y' - z'))) ≤ 0 := by
        rw [neg_nonpos]
        exact mul_nonneg hδ.le hS
      linarith
    · intro heq
      have hS0 : P.ρ * (y' - P.poolingQuantity q) ^ 2 + (1 - P.ρ) * (z' - P.poolingQuantity q) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (P.separatingLow q - P.separatingHigh q) * (y' - z') = 0 := by
        have h0 : -(P.δ * (P.ρ * (y' - P.poolingQuantity q) ^ 2 +
          (1 - P.ρ) * (z' - P.poolingQuantity q) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (P.separatingLow q - P.separatingHigh q) * (y' - z'))) = 0 := by
          rw [← h]
          linarith
        rw [neg_eq_zero] at h0
        exact (mul_eq_zero.mp h0).resolve_left hδ.ne'
      have h2 : P.ρ * (y' - P.poolingQuantity q) ^ 2 = 0 := by linarith
      have h3 : (1 - P.ρ) * (z' - P.poolingQuantity q) ^ 2 = 0 := by linarith
      have e2 := (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h2).resolve_left hρ0.ne')
      have e3 := (pow_eq_zero_iff two_ne_zero).mp
        ((mul_eq_zero.mp h3).resolve_left (by linarith : (1 : ℝ) - P.ρ ≠ 0))
      constructor <;> linarith
  · have hν' : (1 : ℝ) - P.ν ≠ 0 := by linarith
    have hdiff : P.separatingHigh q - P.separatingLow q =
        q * (P.rh - P.ν * P.rl) / (2 * (1 - P.ν)) := by
      rw [hY, hZ]
      simp only [Params.kappa, Params.deltaR]
      field_simp
      ring
    have h2ν : (0 : ℝ) < 2 * (1 - P.ν) := by linarith
    constructor
    · intro h
      have h1 : 0 < q * (P.rh - P.ν * P.rl) / (2 * (1 - P.ν)) := by rw [← hdiff]; linarith
      have h2 := (div_pos_iff_of_pos_right h2ν).mp h1
      have h3 := (mul_pos_iff_of_pos_left hq).mp h2
      linarith
    · intro h
      have : 0 < q * (P.rh - P.ν * P.rl) / (2 * (1 - P.ν)) :=
        div_pos (mul_pos hq (by linarith)) h2ν
      linarith
