-- Prove2me | solution 1 for WeinbergLeptons.eq15_charge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:17:28.978552+00:00
-- url     : https://prove2.me/submissions/7add2e9f-500e-48b4-ac75-93cb2ba26637

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
theorem solution (g g' : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) (T3 Y : ℝ) (V : Fin 4 → ℝ) :
    g * T3 * V 2 + g' * Y * V 3 =
      -electricCharge g g' * (T3 - Y) * (photonVec g g' ⬝ᵥ V) +
        (g ^ 2 * T3 + g' ^ 2 * Y) / Real.sqrt (g ^ 2 + g' ^ 2) * (zVec g g' ⬝ᵥ V) := by
  have hNp : 0 < Real.sqrt (g ^ 2 + g' ^ 2) := Real.sqrt_pos.2 hN
  have hN2 : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt hN.le
  have hi : (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * (g ^ 2 + g' ^ 2) = 1 := by
    have hne := hNp.ne'
    field_simp
    linarith [hN2]
  rw [wl_zdot, wl_pdot]
  unfold electricCharge
  linear_combination (-(g * T3 * V 2 + g' * Y * V 3)) * hi
