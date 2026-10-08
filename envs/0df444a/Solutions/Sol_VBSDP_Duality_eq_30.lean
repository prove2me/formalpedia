-- Prove2me | solution 1 for VBSDP.Duality.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:01:55.976646+00:00
-- url     : https://prove2.me/submissions/47391ac7-fbc8-460c-be9c-10f04f302127

import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_IsDualFeasible
open VBSDP.Duality
open scoped Matrix MatrixOrder

theorem solution {m n : ℕ} (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z) :
    c ⬝ᵥ x + (Z * F₀).trace = (∑ i, (Z * F i).trace * x i) + (Z * F₀).trace ∧
      (∑ i, (Z * F i).trace * x i) + (Z * F₀).trace =
        (Z * lmi F₀ F x).trace ∧
      0 ≤ (Z * lmi F₀ F x).trace := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.trace_mul_comm Z, hZ.2, dotProduct]
  · simp only [lmi, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    simp only [mul_comm, add_comm]
  · obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.1.nonneg
    have hn := (hx.mul_mul_conjTranspose_same b).trace_nonneg
    have heq : (b * lmi F₀ F x * bᴴ).trace = (Z * lmi F₀ F x).trace := by
      rw [hb, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle]
    rwa [heq] at hn

#print axioms solution
