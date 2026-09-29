-- Prove2me | solution 1 for RobustLS.Structured.sdp32_iff_calF
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:20:49.714539+00:00
-- url     : https://prove2.me/submissions/f9bcc7c6-6292-413b-8bdd-6f32c96d6a7c

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

theorem aux_s32_hval {n m : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ)
    (x : Fin m → ℝ) : hval A0 b0 x = ∑ k, (A0 *ᵥ x - b0) k * (A0 *ᵥ x - b0) k := by
  unfold hval eucNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [sq]

end RobustLS.Structured

open RobustLS.Structured

theorem solution {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (lam τ : ℝ) (x : Fin m → ℝ) :
    SDP32Feasible A0 A b0 b lam τ x ↔ (calF A0 A b0 b x lam τ).PosSemidef := by
  set B : Matrix (Unit ⊕ Fin p) (Fin n) ℝ :=
    Matrix.of fun i k => Sum.elim (fun _ => (A0 *ᵥ x - b0) k) (fun j => Mx A b x k j) i with hB
  have hC : (Matrix.of fun k i => Sum.elim (fun _ => (A0 *ᵥ x - b0) k)
      (fun j => Mx A b x k j) i : Matrix (Fin n) (Unit ⊕ Fin p) ℝ) = Bᴴ := by
    ext k i
    simp [hB, conjTranspose_apply]
  unfold SDP32Feasible sdp32Matrix
  have : Invertible (1 : Matrix (Fin n) (Fin n) ℝ) := invertibleOne
  rw [hC, ← hB, Matrix.PosDef.fromBlocks₂₂ _ _ (PosDef.one (n := Fin n) (R := ℝ)), inv_one,
    Matrix.mul_one]
  have hBB : B * Bᴴ = hgFBlock A0 A b0 b x := by
    ext (i | i) (j | j)
    · simp [hB, hgFBlock, mul_apply, aux_s32_hval]
    · simp [hB, hgFBlock, mul_apply, gvec, mulVec, dotProduct, mul_comm]
    · simp [hB, hgFBlock, mul_apply, gvec, mulVec, dotProduct]
    · simp [hB, hgFBlock, mul_apply, Fmat]
  rw [hBB]
  unfold hgFBlock calF
  apply iff_of_eq
  congr 1
  ext (i | i) (j | j) <;> simp
