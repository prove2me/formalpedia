-- Prove2me | solution 1 for QuantumLTF.Membership.abs_gridPoint_le_half
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:53:10.769815+00:00
-- url     : https://prove2.me/submissions/1b639995-85c9-44da-bb60-97fa162fdc70

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods

open QAlgorithms

theorem solution (b : ℕ) (z : Qubits b) : |gridPoint b z| ≤ 1 / 2 := by
  rw [abs_le]
  have hp : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hj0 : (0 : ℝ) ≤ bitsToNat z := by positivity
  have hjN : bitsToNat z < 2 ^ b := by
    simpa [bitsEquivFin_apply] using (bitsEquivFin b z).isLt
  have hj : (bitsToNat z : ℝ) < (2 : ℝ) ^ b := by exact_mod_cast hjN
  have hjgapN : bitsToNat z + 1 ≤ 2 ^ b := Nat.succ_le_iff.mpr hjN
  have hjgap : (bitsToNat z : ℝ) + 1 ≤ (2 : ℝ) ^ b := by exact_mod_cast hjgapN
  have hinv : (2 : ℝ) ^ b * ((2 : ℝ) ^ b)⁻¹ = 1 := by field_simp
  have hstep : ((2 : ℝ) ^ (b + 1))⁻¹ =
      (1 / 2 : ℝ) * ((2 : ℝ) ^ b)⁻¹ := by
    rw [pow_succ]
    field_simp
  have hjscale : ((bitsToNat z : ℝ) + 1) * ((2 : ℝ) ^ b)⁻¹ ≤ 1 := by
    calc
      ((bitsToNat z : ℝ) + 1) * ((2 : ℝ) ^ b)⁻¹ ≤
          (2 : ℝ) ^ b * ((2 : ℝ) ^ b)⁻¹ :=
        mul_le_mul_of_nonneg_right hjgap (inv_nonneg.mpr hp.le)
      _ = 1 := hinv
  constructor <;> simp only [gridPoint] <;>
    rw [hstep] <;>
    nlinarith [mul_nonneg hj0 (inv_nonneg.mpr hp.le), hjscale]
