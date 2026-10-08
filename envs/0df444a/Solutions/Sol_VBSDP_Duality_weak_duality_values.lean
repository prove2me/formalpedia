-- Prove2me | solution 1 for VBSDP.Duality.weak_duality_values
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:41:58.665984+00:00
-- url     : https://prove2.me/submissions/bafca980-baa8-4647-b608-deb8621b42e2

import Definitions.Def_VBSDP_Duality_pStar
import Definitions.Def_VBSDP_Duality_dStar
open VBSDP.Duality
open scoped Matrix MatrixOrder

private theorem weak_pair {m n : ℕ} (c : Fin m → ℝ)
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


theorem solution {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    dStar c F₀ F ≤ pStar c F₀ F := by
  apply sSup_le
  rintro _ ⟨Z, hZ, rfl⟩
  apply le_sInf
  rintro _ ⟨x, hx, rfl⟩
  change ((-(F₀ * Z).trace : ℝ) : EReal) ≤ ((c ⬝ᵥ x : ℝ) : EReal)
  exact_mod_cast weak_pair c F₀ F x Z hx hZ

#print axioms solution
