-- Prove2me | solution 1 for QuantumSDP18.DensityBE.sandwich_eq_flag0
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:02:22.538647+00:00
-- url     : https://prove2.me/submissions/7df1916e-4b25-412f-b098-0cd692e88174

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

set_option autoImplicit false
open scoped Kronecker ComplexOrder
open QuantumSDP18.DensityBE

lemma sandwich_apply {w c : ℕ} (φ : Reg w c → ℂ) (i j : QAlgorithms.Qubits w) :
    sandwich φ i j = ∑ t : QAlgorithms.Qubits c, star (φ (j, false, t)) * φ (i, false, t) := by
  simp only [sandwich, Matrix.of_apply, swapReg, swapEquiv, Equiv.coe_fn_mk]
  rw [Finset.sum_comm]
  simp only [Prod.mk.injEq, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [ite_and]
  have h : ∀ x : Reg w c, (∑ y : Reg w c, if i = x.1 then if false = x.2.1 then
      (if y = (j, false, x.2.2) then star (φ y) * φ x else 0) else 0 else 0) =
      if i = x.1 ∧ false = x.2.1 then star (φ (j, false, x.2.2)) * φ x else 0 := by
    intro x
    by_cases h1 : i = x.1 <;> by_cases h2 : false = x.2.1 <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp

theorem solution {w c : ℕ} (φ : Reg w c → ℂ) :
    sandwich φ = sandwich (flag0 φ) := by
  ext i j
  rw [sandwich_apply, sandwich_apply]
  simp [flag0]
