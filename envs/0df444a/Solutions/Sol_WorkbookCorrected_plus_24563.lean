-- Prove2me | solution 1 for WorkbookCorrected.plus_24563
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:12:51.890036+00:00
-- url     : https://prove2.me/submissions/5bb7862b-38ef-46d2-8dd4-25f209f038f5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma cube_exists (t : ℝ) : ∃ y : ℝ, y^3=t := by
  have ha := abs_nonneg t
  have hb : |t| ≤ (|t|+1)^3 := by
    nlinarith [sq_nonneg |t|, mul_nonneg (sq_nonneg |t|) ha]
  have hlo : (-(|t|+1))^3 ≤ t := by nlinarith [neg_abs_le t]
  have hhi : t ≤ (|t|+1)^3 := le_trans (le_abs_self t) hb
  have hh := intermediate_value_Icc
    (a := -(|t|+1)) (b := |t|+1) (by linarith : -(|t|+1) ≤ |t|+1)
    (f := fun z : ℝ => z^3) (by fun_prop)
    (show t ∈ Set.Icc ((-(|t|+1))^3) ((|t|+1)^3) from ⟨hlo,hhi⟩)
  rcases hh with ⟨y, _, hy⟩
  exact ⟨y,hy⟩
theorem solution (f : ℝ → ℝ) :
    (∀ x y : ℝ, y^3 = 1-x^3 → f x + 2*f y = x^3) ↔
    (∀ x : ℝ, f x = 2/3-x^3) := by
  constructor
  · intro hf x
    obtain ⟨y,hy⟩ := cube_exists (1-x^3)
    have hxy := hf x y hy
    have hyx := hf y x (by linarith only [hy])
    linarith only [hxy,hyx,hy]
  · intro hf x y hy
    rw [hf x,hf y]
    linarith only [hy]
example : (∀ (f : ℝ → ℝ),
    (∀ x y : ℝ, y^3 = 1-x^3 → f x + 2*f y = x^3) ↔
    (∀ x : ℝ, f x = 2/3-x^3)) := @solution
#print axioms solution
