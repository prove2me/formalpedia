-- Prove2me | solution 1 for VBSDP.Duality.weak_duality_31
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:41:56.114668+00:00
-- url     : https://prove2.me/submissions/64bc0bc7-150a-4e34-be3f-957bb1224cd1

import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_IsDualFeasible
open VBSDP.Duality
open scoped Matrix MatrixOrder

theorem solution {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z) :
    -(F₀ * Z).trace ≤ c ⬝ᵥ x := by
  have htrace : (lmi F₀ F x * Z).trace = (F₀ * Z).trace + c ⬝ᵥ x := by
    simp only [lmi, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
      hZ.2, dotProduct]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.1.nonneg
  have hn := (hx.mul_mul_conjTranspose_same b).trace_nonneg
  have heq : (b * lmi F₀ F x * bᴴ).trace = (lmi F₀ F x * Z).trace := by
    rw [hb, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle']
    simp only [Matrix.mul_assoc]
  rw [heq, htrace] at hn
  linarith

#print axioms solution
