-- Prove2me | solution 1 for VaryingConstants.planck_units
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:14:41.064049+00:00
-- url     : https://prove2.me/submissions/3051ac20-e4c3-4eec-ad0d-733ca23d7e75

import Mathlib
import Definitions.Def_VaryingConstants_units

set_option autoImplicit false

open VaryingConstants in
theorem f6904621_reduce (c G hbar : ℝ) (s : Fin 3 → ℝ) :
    IsNaturalUnitsFor planckDims id ![c, G, hbar] s ↔
      (0 < s 0 ∧ 0 < s 1 ∧ 0 < s 2) ∧
      (c * (s 0 * (s 2)⁻¹) = 1 ∧ G * (s 0 ^ 3 * (s 1)⁻¹ * ((s 2) ^ 2)⁻¹) = 1 ∧
        hbar * (s 0 ^ 2 * s 1 * (s 2)⁻¹) = 1) := by
  simp only [IsNaturalUnitsFor, IsPositive, unitRescale, Fin.forall_fin_succ, Fin.prod_univ_three,
    planckDims, id, IsEmpty.forall_iff, and_true]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_neg_one,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

open VaryingConstants in
theorem f6904621_sqrt_aux (c G hbar : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar) :
    Real.sqrt (c ^ 5 / (G * hbar)) = c * Real.sqrt (c ^ 3 / (G * hbar)) ∧
    Real.sqrt (G / (hbar * c)) = c / (hbar * Real.sqrt (c ^ 3 / (G * hbar))) := by
  have hA : 0 < Real.sqrt (c ^ 3 / (G * hbar)) := Real.sqrt_pos.mpr (by positivity)
  have hA2 : Real.sqrt (c ^ 3 / (G * hbar)) ^ 2 = c ^ 3 / (G * hbar) :=
    Real.sq_sqrt (by positivity)
  constructor
  · rw [show c ^ 5 / (G * hbar) = c ^ 2 * (c ^ 3 / (G * hbar)) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hc.le]
  · rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    generalize hAdef : Real.sqrt (c ^ 3 / (G * hbar)) = A at hA hA2 ⊢
    field_simp
    rw [hA2]
    field_simp

open VaryingConstants in
theorem solution (c G hbar : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (s : Fin 3 → ℝ) :
    IsNaturalUnitsFor planckDims id ![c, G, hbar] s ↔
      s = ![Real.sqrt (c ^ 3 / (G * hbar)), Real.sqrt (G / (hbar * c)),
            Real.sqrt (c ^ 5 / (G * hbar))] := by
  rw [f6904621_reduce]
  obtain ⟨h5, hB⟩ := f6904621_sqrt_aux c G hbar hc hG hh
  rw [h5, hB]
  have hA2 : Real.sqrt (c ^ 3 / (G * hbar)) ^ 2 = c ^ 3 / (G * hbar) :=
    Real.sq_sqrt (by positivity)
  have hA : 0 < Real.sqrt (c ^ 3 / (G * hbar)) := Real.sqrt_pos.mpr (by positivity)
  generalize Real.sqrt (c ^ 3 / (G * hbar)) = A at hA hA2 ⊢
  constructor
  · rintro ⟨⟨ha, hb, ht⟩, e1, e2, e3⟩
    have ht' : s 2 = c * s 0 := by
      field_simp at e1
      linarith
    have hb' : s 1 = c / (hbar * s 0) := by
      rw [ht'] at e3
      field_simp at e3 ⊢
      nlinarith
    have ha2 : s 0 ^ 2 = c ^ 3 / (G * hbar) := by
      rw [ht', hb'] at e2
      field_simp at e2 ⊢
      nlinarith
    have hA0 : s 0 = A := by
      have h1 : s 0 ^ 2 = A ^ 2 := by rw [ha2, hA2]
      nlinarith [sq_nonneg (s 0 - A), sq_nonneg (s 0 + A)]
    funext i
    fin_cases i
    · simp [hA0]
    · simp [hb', hA0]
    · simp [ht', hA0]
  · rintro rfl
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨hA, by positivity, by positivity⟩, ?_, ?_, ?_⟩
    · field_simp
    · field_simp
      rw [hA2]
      field_simp
    · field_simp
