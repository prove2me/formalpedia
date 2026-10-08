-- Prove2me | solution 1 for VBSDP.Potential.duality_gap_32
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:11:11.478219+00:00
-- url     : https://prove2.me/submissions/80d9e4a0-2870-4001-ab75-1a0898cb8d59

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

theorem solution {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : (VBSDP.Duality.lmi F₀ F x).PosSemidef) (hZ : Z.PosSemidef)
    (hdual : ∀ i, (F i * Z).trace = c i) :
    c ⬝ᵥ x + (F₀ * Z).trace = (VBSDP.Duality.lmi F₀ F x * Z).trace := by
  simp only [VBSDP.Duality.lmi, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, hdual, smul_eq_mul, dotProduct]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

#print axioms solution
