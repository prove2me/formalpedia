-- Prove2me | solution 1 for SupplierLearning.period_two_double
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:44:01.8885+00:00
-- url     : https://prove2.me/submissions/c49dcd52-6eb1-4208-9a2b-1e25b531bfee

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_separatingHigh
import Definitions.Def_SupplierLearning_Params_separatingLow
import Definitions.Def_SupplierLearning_Params_poolingQuantity
import Definitions.Def_SupplierLearning_Params_IsPeriodTwoMax

set_option autoImplicit false

open SupplierLearning

theorem solution (P : Params) (hP : P.Standing) {q : ℝ} (hq : 0 ≤ q)
    (hk : P.cl < P.ch - P.rh * q) :
    (P.separatingLow q < P.separatingHigh q →
      P.IsPeriodTwoMax q (P.separatingHigh q) (P.separatingLow q)) ∧
    (P.separatingHigh q ≤ P.separatingLow q →
      P.IsPeriodTwoMax q (P.poolingQuantity q) (P.poolingQuantity q)) ∧
    P.ρ * P.separatingHigh q + (1 - P.ρ) * P.separatingLow q = P.poolingQuantity q := by
  have hδ := hP.δ_pos
  have hρ0 := hP.ρ_pos
  have hρ1 := hP.ρ_lt_one
  have hρne : P.ρ ≠ 0 := hρ0.ne'
  have hw1 : 0 < P.δ * P.ρ := mul_pos hδ hρ0
  have hw2 : 0 < P.δ * (1 - P.ρ) := mul_pos hδ (by linarith)
  have hk' : ¬ (P.ch - P.rh * q ≤ P.cl) := not_le.mpr hk
  have hY : P.separatingHigh q = (P.a₂ - P.ch + P.rh * q) / 2 +
      1 / 2 * P.kappa * ((P.rh - P.ρ * P.rl) / P.ρ) * q - 1 / 2 * P.kappa * (1 / P.ρ) * P.deltaC := by
    rw [Params.separatingHigh, if_neg hk']
  have hZ : P.separatingLow q = (P.a₂ - P.ch) / 2 - 1 / 2 * P.kappa * P.rh * q := by
    rw [Params.separatingLow, if_neg hk']
  set Y := P.separatingHigh q with hYdef
  set Z := P.separatingLow q with hZdef
  set T := P.poolingQuantity q with hTdef
  let G : ℝ → ℝ → ℝ := fun y z => P.typeSurplus .h q y z -
    P.kappa * (P.rentFloor q y z + P.δ * (1 - P.ρ) * ((P.deltaC - P.rh * q) * (y - z)))
  have hR : ∀ y z, z ≤ y → P.reducedObjective q y z = G y z := by
    intro y z hzy
    have hm : max 0 ((P.deltaC - P.rh * q) * (y - z)) = (P.deltaC - P.rh * q) * (y - z) := by
      apply max_eq_right
      have h1 : 0 ≤ P.deltaC - P.rh * q := by unfold Params.deltaC; linarith
      exact mul_nonneg h1 (by linarith)
    rw [Params.reducedObjective, Params.rentBound, hm]
  have hsq : ∀ y z y2 z2, G y z - G y2 z2 =
      -(P.δ * P.ρ) * ((y - Y) ^ 2 - (y2 - Y) ^ 2) - P.δ * (1 - P.ρ) * ((z - Z) ^ 2 - (z2 - Z) ^ 2) := by
    intro y z y2 z2
    simp only [G, hY, hZ, Params.typeSurplus, Params.rentFloor, Params.cost, Params.rate, Params.deltaR]
    field_simp
    ring
  have hpool : P.ρ * Y + (1 - P.ρ) * Z = T := by
    rw [hY, hZ, hTdef, Params.poolingQuantity]
    simp only [Params.deltaR]
    field_simp
    ring
  refine ⟨?_, ?_, hpool⟩
  · intro hZY
    refine ⟨hZY.le, fun y' z' hz' => ?_⟩
    rw [hR y' z' hz', hR _ _ hZY.le]
    have hA := mul_nonneg hw1.le (sq_nonneg (y' - Y))
    have hB := mul_nonneg hw2.le (sq_nonneg (z' - Z))
    have hd : G y' z' - G Y Z = -(P.δ * P.ρ * (y' - Y) ^ 2 + P.δ * (1 - P.ρ) * (z' - Z) ^ 2) := by
      rw [hsq]
      ring
    constructor
    · have : -(P.δ * P.ρ * (y' - Y) ^ 2 + P.δ * (1 - P.ρ) * (z' - Z) ^ 2) ≤ 0 := by
        rw [neg_nonpos]
        exact add_nonneg hA hB
      linarith
    · intro heq
      have hsum : P.δ * P.ρ * (y' - Y) ^ 2 + P.δ * (1 - P.ρ) * (z' - Z) ^ 2 = 0 := by
        have : -(P.δ * P.ρ * (y' - Y) ^ 2 + P.δ * (1 - P.ρ) * (z' - Z) ^ 2) = 0 := by
          rw [← hd]; linarith
        linarith
      have h2 : P.δ * P.ρ * (y' - Y) ^ 2 = 0 := by linarith
      have h3 : P.δ * (1 - P.ρ) * (z' - Z) ^ 2 = 0 := by linarith
      have e2 := (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h2).resolve_left hw1.ne')
      have e3 := (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h3).resolve_left hw2.ne')
      constructor <;> linarith
  · intro hYZ
    refine ⟨le_rfl, fun y' z' hz' => ?_⟩
    rw [hR y' z' hz', hR _ _ le_rfl]
    have expand : G y' z' - G T T =
        -(P.δ * (P.ρ * (y' - T) ^ 2 + (1 - P.ρ) * (z' - T) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (Z - Y) * (y' - z'))) := by
      rw [hsq, ← hpool]
      ring
    have hA := mul_nonneg hρ0.le (sq_nonneg (y' - T))
    have hB := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - P.ρ) (sq_nonneg (z' - T))
    have hC : 0 ≤ 2 * P.ρ * (1 - P.ρ) * (Z - Y) * (y' - z') := by
      apply mul_nonneg
      apply mul_nonneg
      · nlinarith
      · linarith
      · linarith
    have hS : 0 ≤ P.ρ * (y' - T) ^ 2 + (1 - P.ρ) * (z' - T) ^ 2 +
        2 * P.ρ * (1 - P.ρ) * (Z - Y) * (y' - z') := by linarith
    constructor
    · have : -(P.δ * (P.ρ * (y' - T) ^ 2 + (1 - P.ρ) * (z' - T) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (Z - Y) * (y' - z'))) ≤ 0 := by
        rw [neg_nonpos]
        exact mul_nonneg hδ.le hS
      linarith
    · intro heq
      have hS0 : P.ρ * (y' - T) ^ 2 + (1 - P.ρ) * (z' - T) ^ 2 +
          2 * P.ρ * (1 - P.ρ) * (Z - Y) * (y' - z') = 0 := by
        have h0 : -(P.δ * (P.ρ * (y' - T) ^ 2 + (1 - P.ρ) * (z' - T) ^ 2 +
            2 * P.ρ * (1 - P.ρ) * (Z - Y) * (y' - z'))) = 0 := by
          rw [← expand]; linarith
        rw [neg_eq_zero] at h0
        exact (mul_eq_zero.mp h0).resolve_left hδ.ne'
      have h2 : P.ρ * (y' - T) ^ 2 = 0 := by linarith
      have h3 : (1 - P.ρ) * (z' - T) ^ 2 = 0 := by linarith
      have e2 := (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h2).resolve_left hρ0.ne')
      have e3 := (pow_eq_zero_iff two_ne_zero).mp
        ((mul_eq_zero.mp h3).resolve_left (by linarith : (1 : ℝ) - P.ρ ≠ 0))
      constructor <;> linarith
