-- Prove2me | solution 1 for Pr6453Tensor.checkBasis_sound
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-09T08:54:00.282419+00:00
-- url     : https://prove2.me/submissions/c62148db-13f9-46e7-a1cf-812fe805aba8

import Definitions.Def_Pr6453_TensorEnc
import Mathlib

set_option autoImplicit false

theorem solution {m n c : ℕ} (row : Fin m → Fin n → (Fin c → ℚ))
    (M : (Fin c → ℚ) →ₗ[ℚ] (Fin c → ℚ)) (read : (Fin c → ℚ) →ₗ[ℚ] (Fin c → ℚ))
    (P : Fin m → Fin n → (Fin c → ℚ))
    (h : Pr6453Tensor.checkBasis row M read P = true) (i : Fin m) (j : Fin n) :
    read (M (Pr6453Tensor.enc row (Pi.single i 1 ⊗ₜ[ℚ] Pi.single j 1))) = P i j := by
  rw [Pr6453Tensor.checkBasis, List.all_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.mp (h i (by simp)) j (by simp))
