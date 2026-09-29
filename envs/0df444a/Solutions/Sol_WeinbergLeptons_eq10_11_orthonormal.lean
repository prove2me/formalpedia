-- Prove2me | solution 1 for WeinbergLeptons.eq10_11_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T00:59:28.899501+00:00
-- url     : https://prove2.me/submissions/3ec9a220-379c-4745-86fa-81d0752e253e

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem wl_zdot (g g' : ℝ) (v : Fin 4 → ℝ) :
    zVec g g' ⬝ᵥ v = (g * v 2 + g' * v 3) / Real.sqrt (g ^ 2 + g' ^ 2) := by
  simp [zVec, dotProduct, Fin.sum_univ_four]
  ring

open WeinbergLeptons Matrix in
theorem wl_pdot (g g' : ℝ) (v : Fin 4 → ℝ) :
    photonVec g g' ⬝ᵥ v = (-g' * v 2 + g * v 3) / Real.sqrt (g ^ 2 + g' ^ 2) := by
  simp [photonVec, dotProduct, Fin.sum_univ_four]
  ring

open WeinbergLeptons Matrix in
theorem solution (g g' : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) :
    zVec g g' ⬝ᵥ zVec g g' = 1 ∧ photonVec g g' ⬝ᵥ photonVec g g' = 1 ∧
      zVec g g' ⬝ᵥ photonVec g g' = 0 := by
  have hNp : 0 < Real.sqrt (g ^ 2 + g' ^ 2) := Real.sqrt_pos.2 hN
  have hN2 : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt hN.le
  have hne : Real.sqrt (g ^ 2 + g' ^ 2) ≠ 0 := hNp.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [wl_zdot]
    simp [zVec]
    field_simp
    linear_combination -hN2
  · rw [wl_pdot]
    simp [photonVec]
    field_simp
    linear_combination -hN2
  · rw [wl_zdot, div_eq_zero_iff]
    left
    simp only [photonVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
    simp
    ring
