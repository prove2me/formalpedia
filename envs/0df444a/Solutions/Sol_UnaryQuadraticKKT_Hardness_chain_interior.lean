-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.chain_interior
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:37:02.696332+00:00
-- url     : https://prove2.me/submissions/edf6d137-47b5-4460-a5b0-ff5c1e515e34

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Chain

set_option autoImplicit false

open UnaryQuadraticKKT.Hardness

theorem solution (k : ℕ) (hk : 1 ≤ k) (s : ℤ) (hs : s = -1 ∨ s = 1)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    ∀ i : Fin (k + 2), -1 < chainMinimizer k s x y i ∧
      chainMinimizer k s x y i < 1 := by
  intro i
  have hi : i.val ≤ k + 1 := by omega
  set a : ℝ := (2 : ℝ) ^ (-(i.val : ℤ)) with ha
  set b : ℝ := (2 : ℝ) ^ ((i.val : ℤ) + 1 - ((k : ℤ) + 2)) with hb
  have ha0 : 0 < a := zpow_pos (by norm_num) _
  have hb0 : 0 < b := zpow_pos (by norm_num) _
  have ha1 : a ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hb1 : b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hxa : a * x ≤ 1 := by nlinarith
  have hyb : b * y ≤ 1 := by nlinarith
  have hxa0 : 0 ≤ a * x := by nlinarith
  have hyb0 : 0 ≤ b * y := by nlinarith
  simp only [chainMinimizer]
  rw [← ha, ← hb]
  rcases hs with rfl | rfl <;> push_cast <;> constructor <;> nlinarith
