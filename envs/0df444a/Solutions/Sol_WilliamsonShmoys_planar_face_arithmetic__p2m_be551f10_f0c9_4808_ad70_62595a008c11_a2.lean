-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_arithmetic__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:37.981922+00:00
-- url     : https://prove2.me/submissions/d874b297-f060-43af-b070-c8f8f6bb10c4

import Mathlib

set_option autoImplicit false

theorem solution (n e : ℕ) (hn : 3 ≤ n) (hedge : e + 6 = 3 * n) :
    ∃ (F : Type) (_ : Fintype F) (length : F → ℕ),
      (∑ f : F, (length f : ℤ) = 2 * (e : ℤ)) ∧
      ((n : ℤ) - (e : ℤ) + (Fintype.card F : ℤ) = 2) ∧
      (∀ f : F, length f = 3) ∧
      ((∑ f : F, (length f : ℤ)) = 3 * (Fintype.card F : ℤ)) := by
  let m : ℕ := 2 * n - 4
  have hm : m + 4 = 2 * n := by
    dsimp [m]
    omega
  have hcard : (Fintype.card (Fin m) : ℤ) = 2 * (n : ℤ) - 4 := by
    simp
    omega
  have hedgeZ : (e : ℤ) + 6 = 3 * (n : ℤ) := by
    exact_mod_cast hedge
  refine ⟨Fin m, inferInstance, fun _ => 3, ?_, ?_, ?_, ?_⟩
  · simp [Finset.sum_const, nsmul_eq_mul]
    omega
  · rw [hcard]
    omega
  · intro f
    rfl
  · simp [Finset.sum_const, nsmul_eq_mul]
    omega