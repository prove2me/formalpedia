-- Prove2me | solution 1 for WeinbergLeptons.mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:25:15.88164+00:00
-- url     : https://prove2.me/submissions/5bb66c53-673a-4a90-8070-cd1784432a4d

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem solution (g g' lam : ℝ) (hg : g ≠ 0) (hg' : g' ≠ 0) (hlam : lam ≠ 0) :
    Real.sqrt 2 * electricCharge g g' ^ 2 / (8 * weakCoupling g lam) < wMass g lam ^ 2 ∧
      wMass g lam ^ 2 < zMass g g' lam ^ 2 ∧
      4 * (Real.sqrt 2 * electricCharge g g' ^ 2 / (8 * weakCoupling g lam)) ≤ zMass g g' lam ^ 2 := by
  have hS : 0 < g ^ 2 + g' ^ 2 := by positivity
  have hN2 : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt hS.le
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hSne : g ^ 2 + g' ^ 2 ≠ 0 := hS.ne'
  have hL : Real.sqrt 2 * electricCharge g g' ^ 2 / (8 * weakCoupling g lam)
      = lam ^ 2 * g ^ 2 * g' ^ 2 / (4 * (g ^ 2 + g' ^ 2)) := by
    unfold electricCharge weakCoupling wMass
    rw [div_pow, hN2]
    field_simp
    ring
  have hWm : wMass g lam ^ 2 = lam ^ 2 * g ^ 2 / 4 := by unfold wMass; ring
  have hZm : zMass g g' lam ^ 2 = lam ^ 2 * (g ^ 2 + g' ^ 2) / 4 := by
    unfold zMass; rw [div_pow, mul_pow, hN2]; norm_num
  rw [hL, hWm, hZm]
  have hl2 : 0 < lam ^ 2 := by positivity
  have hg2 : 0 < g ^ 2 := by positivity
  have hg'2 : 0 < g' ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have h4 : 0 < lam ^ 2 * g ^ 2 * g ^ 2 := by positivity
    nlinarith [h4]
  · have h4 : 0 < lam ^ 2 * g' ^ 2 := by positivity
    nlinarith [h4]
  · rw [show 4 * (lam ^ 2 * g ^ 2 * g' ^ 2 / (4 * (g ^ 2 + g' ^ 2)))
        = lam ^ 2 * g ^ 2 * g' ^ 2 / (g ^ 2 + g' ^ 2) by field_simp]
    rw [div_le_div_iff₀ hS (by norm_num)]
    nlinarith [mul_nonneg (sq_nonneg lam) (sq_nonneg (g ^ 2 - g' ^ 2))]
