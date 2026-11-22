-- Prove2me | solution 1 for ShiShallow.mulVec_majority_inclusion_exclusion_of_common_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T20:15:26.698506+00:00
-- url     : https://prove2.me/submissions/88804e86-b56a-4958-91e4-38f52c577b52

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

private theorem shiAsm_mulVec_mul {n : ℕ} {X Y : Op n} {φ : Bits n → ℂ} {x y : ℂ}
    (hX : Matrix.mulVec X φ = x • φ) (hY : Matrix.mulVec Y φ = y • φ) :
    Matrix.mulVec (X * Y) φ = (x * y) • φ := by
  rw [← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul, hX, smul_smul, mul_comm y x]

theorem solution {n : ℕ} (A B C : Op n) (φ : Bits n → ℂ) (α β γ : ℂ)
    (hA : Matrix.mulVec A φ = α • φ) (hB : Matrix.mulVec B φ = β • φ)
    (hC : Matrix.mulVec C φ = γ • φ) :
    Matrix.mulVec (A * B + B * C + C * A - (2 : ℂ) • (A * B * C)) φ
      = (α * β + β * γ + γ * α - 2 * (α * β * γ)) • φ := by
  have hAB := shiAsm_mulVec_mul hA hB
  have hBC := shiAsm_mulVec_mul hB hC
  have hCA := shiAsm_mulVec_mul hC hA
  have hABC := shiAsm_mulVec_mul hAB hC
  first
  | (simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
        hAB, hBC, hCA, hABC]; module; done)
  | (simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
     rw [hAB, hBC, hCA, hABC]; module; done)
  | (rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
        hAB, hBC, hCA, hABC]; module; done)
  | (simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
        hAB, hBC, hCA, hABC]
     ext x; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
