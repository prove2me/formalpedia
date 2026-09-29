-- Prove2me | solution 1 for RobustSDP.Unstructured.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:53:45.987543+00:00
-- url     : https://prove2.me/submissions/22b25c9a-e777-4264-ba1d-0b2aeef3639f

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

theorem aux_eq21_shift {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (hab : b ≤ a)
    (h : (F - a • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    (F - b • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have e : F - b • (1 : Matrix (Fin n) (Fin n) ℝ) =
      (F - a • (1 : Matrix (Fin n) (Fin n) ℝ)) + (a - b) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [sub_smul]; abel
  rw [e]
  exact h.add (Matrix.PosSemidef.one.smul (by linarith))

end RobustSDP.Unstructured

open RobustSDP.Unstructured
open Matrix
open scoped Matrix.Norms.L2Operator

theorem solution {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    (∃ τ : ℝ, 0 < τ ∧ (affineMap Fs x -
        (τ + ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ↔
      (affineMap Fs x -
        (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  set S := ∑ i, x i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hq : 0 < Real.sqrt (S + 1) := Real.sqrt_pos.mpr (by linarith)
  have hq2 : Real.sqrt (S + 1) ^ 2 = S + 1 := Real.sq_sqrt (by linarith)
  set s := ρ * Real.sqrt (S + 1) with hs
  have hs0 : 0 < s := mul_pos hρ hq
  have hc : ρ ^ 2 * (1 + S) = s ^ 2 := by rw [hs, mul_pow, hq2]; ring
  constructor
  · rintro ⟨τ, hτ, h⟩
    refine aux_eq21_shift _ _ _ ?_ h
    rw [hc]
    have key : τ + s ^ 2 / τ - 2 * s = (τ - s) ^ 2 / τ := by
      field_simp; ring
    have : 0 ≤ (τ - s) ^ 2 / τ := div_nonneg (sq_nonneg _) hτ.le
    have e2 : 2 * ρ * Real.sqrt (S + 1) = 2 * s := by rw [hs]; ring
    rw [e2]; linarith
  · intro h
    refine ⟨s, hs0, ?_⟩
    have e : s + ρ ^ 2 * (1 + S) / s = 2 * ρ * Real.sqrt (S + 1) := by
      rw [hc, hs]; field_simp; ring
    rw [e]; exact h
