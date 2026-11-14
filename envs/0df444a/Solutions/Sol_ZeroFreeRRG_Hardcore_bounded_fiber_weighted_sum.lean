-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.bounded_fiber_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:12:32.787939+00:00
-- url     : https://prove2.me/submissions/ba358af1-c011-4eeb-898d-6e4694835cd0

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution {X : Type*} [DecidableEq X]
    (T H : Finset X) (F : X → X) (w : X → ℝ) (B : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ y ∈ H, 0 ≤ w y)
    (hmap : ∀ x ∈ T, F x ∈ H)
    (hfiber : ∀ y ∈ H, (T.filter (fun x => F x = y)).card ≤ B)
    (hbound : ∀ x ∈ T, w x ≤ C * w (F x)) :
    (∑ x ∈ T, w x) ≤ (B : ℝ) * C * ∑ y ∈ H, w y := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmap w]
  calc
    (∑ y ∈ H, ∑ x ∈ T with F x = y, w x) ≤
        ∑ y ∈ H, ((B : ℝ) * (C * w y)) := by
      apply Finset.sum_le_sum
      intro y hy
      let fiber := T.filter (fun x => F x = y)
      have hcard : (fiber.card : ℝ) ≤ B := by exact_mod_cast hfiber y hy
      have hpos : 0 ≤ C * w y := mul_nonneg hC (hw y hy)
      calc
        (∑ x ∈ fiber, w x) ≤ fiber.card • (C * w y) := by
          apply Finset.sum_le_card_nsmul
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          simpa [hx'.2] using hbound x hx'.1
        _ = (fiber.card : ℝ) * (C * w y) := by simp
        _ ≤ (B : ℝ) * (C * w y) := mul_le_mul_of_nonneg_right hcard hpos
    _ = (B : ℝ) * C * ∑ y ∈ H, w y := by rw [Finset.mul_sum]; congr 1; funext y; ring
