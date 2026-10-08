-- Prove2me | solution 1 for VBSDP.Duality.compl_slackness
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:41:57.557922+00:00
-- url     : https://prove2.me/submissions/aa565587-bc81-43a1-b039-b3a4a919e849

import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_IsDualFeasible
open VBSDP.Duality
open scoped Matrix MatrixOrder

private theorem trace_zero_product {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (htr : (A * B).trace = 0) :
    A * B = 0 := by
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have hz : a * bᴴ = 0 := by
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    calc
      (a * bᴴ * (a * bᴴ)ᴴ).trace = (star a * a * (star b * b)).trace := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.star_eq_conjTranspose]
        rw [← Matrix.mul_assoc (a * bᴴ) b aᴴ, Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
      _ = 0 := htr
  calc
    star a * a * (star b * b) = star a * (a * bᴴ) * b := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    _ = 0 := by rw [hz]; simp


theorem solution {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z)
    (hopt : c ⬝ᵥ x = -(F₀ * Z).trace) :
    Z * lmi F₀ F x = 0 := by
  apply trace_zero_product Z (lmi F₀ F x) hZ.1 hx
  rw [Matrix.trace_mul_comm]
  have htrace : (lmi F₀ F x * Z).trace = (F₀ * Z).trace + c ⬝ᵥ x := by
    simp only [lmi, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
      hZ.2, dotProduct]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [htrace, hopt]
  ring

#print axioms solution
