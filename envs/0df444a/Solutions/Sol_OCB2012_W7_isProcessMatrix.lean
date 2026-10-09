-- Prove2me | solution 1 for OCB2012.W7_isProcessMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:04:55.581709+00:00
-- url     : https://prove2.me/submissions/b25c7047-e598-48e2-8e74-920bc5a560d2

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

/-- `Tr[(X ⊗ 𝟙) M] = Tr[X · Tr₂ M]`. -/
lemma trace_kron_one_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (X : Matrix α α ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    ((X ⊗ₖ (1 : Matrix β β ℂ)) * M).trace = (X * ptrace₂ M).trace := by
  simp only [trace, diag, mul_apply, Fintype.sum_prod_type, kronecker_apply, one_apply,
    ptrace₂, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_ite, ite_mul]

lemma σz_mul_σz : σz * σz = 1 := by
  rw [σz, mul_fin_two, one_fin_two]; norm_num

lemma σx_mul_σx : σx * σx = 1 := by
  rw [σx, mul_fin_two, one_fin_two]; norm_num

lemma σz_mul_σx : σz * σx = (-1 : ℂ) • (σx * σz) := by
  rw [σz, σx, mul_fin_two, mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

lemma trace_σz : σz.trace = 0 := by simp [σz, trace_fin_two]

lemma trace_σx : σx.trace = 0 := by simp [σx, trace_fin_two]

lemma σz_herm : σz.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σz]

lemma σx_herm : σx.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σx]


/-- The two correlation terms of Eq. (7). -/
abbrev S7 : Matrix ((Qubit × Qubit) × (Qubit × Qubit)) ((Qubit × Qubit) × (Qubit × Qubit)) ℂ :=
  ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ σz) ⊗ₖ (σz ⊗ₖ (1 : Matrix Qubit Qubit ℂ))
abbrev T7 : Matrix ((Qubit × Qubit) × (Qubit × Qubit)) ((Qubit × Qubit) × (Qubit × Qubit)) ℂ :=
  (σz ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) ⊗ₖ (σx ⊗ₖ σz)

lemma S7_mul_S7 : S7 * S7 = 1 := by
  simp only [S7, ← mul_kronecker_mul, Matrix.one_mul, σz_mul_σz, one_kronecker_one]

lemma T7_mul_T7 : T7 * T7 = 1 := by
  simp only [T7, ← mul_kronecker_mul, Matrix.one_mul, σz_mul_σz, σx_mul_σx, one_kronecker_one]

lemma S7_mul_T7_add : S7 * T7 + T7 * S7 = 0 := by
  simp only [S7, T7, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, σz_mul_σx,
    smul_kronecker, kronecker_smul]
  rw [neg_one_smul, neg_add_cancel]

lemma S7_herm : S7.IsHermitian := by
  simp only [IsHermitian, S7, conjTranspose_kronecker, conjTranspose_one, σz_herm.eq]

lemma T7_herm : T7.IsHermitian := by
  simp only [IsHermitian, T7, conjTranspose_kronecker, conjTranspose_one, σz_herm.eq, σx_herm.eq]

lemma W7_eq : W7 = (1 / 4 : ℂ) • (1 + ((1 / Real.sqrt 2 : ℝ) : ℂ) • (S7 + T7)) := rfl

lemma W7_posSemidef : W7.PosSemidef := by
  set c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  set K := c • (S7 + T7) with hK
  have hc : c * c = 1 / 2 := by
    simp only [c, ← Complex.ofReal_mul]
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hcs : star c = c := by simp [c]
  have hKh : Kᴴ = K := by
    rw [hK, conjTranspose_smul, conjTranspose_add, S7_herm.eq, T7_herm.eq, hcs]
  have hKK : K * K = 1 := by
    rw [hK, smul_mul_smul_comm, hc, add_mul, mul_add, mul_add, S7_mul_S7, T7_mul_T7]
    rw [show (1 : Matrix _ _ ℂ) + S7 * T7 + (T7 * S7 + 1) = (S7 * T7 + T7 * S7) + 2 by
      rw [← one_add_one_eq_two (R := Matrix ((Qubit × Qubit) × (Qubit × Qubit))
        ((Qubit × Qubit) × (Qubit × Qubit)) ℂ)]; abel, S7_mul_T7_add, zero_add]
    rw [show (2 : Matrix ((Qubit × Qubit) × (Qubit × Qubit)) ((Qubit × Qubit) × (Qubit × Qubit)) ℂ)
      = (2 : ℂ) • 1 by rw [two_smul, one_add_one_eq_two (R := Matrix ((Qubit × Qubit) × (Qubit × Qubit))
        ((Qubit × Qubit) × (Qubit × Qubit)) ℂ)], smul_smul]
    norm_num
  have h1K : 1 + K = (1 / 2 : ℂ) • ((1 + K)ᴴ * (1 + K)) := by
    rw [conjTranspose_add, conjTranspose_one, hKh, add_mul, mul_add, mul_add, hKK,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    rw [show (1 : Matrix _ _ ℂ) + K + (K + 1) = (2 : ℂ) • (1 + K) by
      rw [two_smul]; abel, smul_smul]; norm_num
  rw [W7_eq, ← hK, h1K, smul_smul]
  refine (posSemidef_conjTranspose_mul_self _).smul ?_
  rw [show (1 / 4 * (1 / 2) : ℂ) = ((1 / 8 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_le_real.mpr (by norm_num)

end OCB2012Sol

open OCB2012 OCB2012Sol

theorem solution : OCB2012.IsProcessMatrix OCB2012.W7 := by
  refine ⟨W7_posSemidef, fun MA MB hA hB => ?_⟩
  have hA2 : ∀ X : Matrix Qubit Qubit ℂ, ((X ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) * MA).trace = X.trace :=
    fun X => by rw [trace_kron_one_mul, hA.2, Matrix.mul_one]
  have hB2 : ∀ X : Matrix Qubit Qubit ℂ, ((X ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) * MB).trace = X.trace :=
    fun X => by rw [trace_kron_one_mul, hB.2, Matrix.mul_one]
  have htrA : MA.trace = 2 := by
    have := hA2 1; rwa [one_kronecker_one, Matrix.one_mul, trace_one, Fintype.card_fin] at this
  have htrB : MB.trace = 2 := by
    have := hB2 1; rwa [one_kronecker_one, Matrix.one_mul, trace_one, Fintype.card_fin] at this
  rw [prob, W7_eq, Matrix.smul_mul, add_mul, Matrix.smul_mul, add_mul, trace_smul, trace_add,
    trace_smul, trace_add, Matrix.one_mul, trace_kronecker, S7, T7, ← mul_kronecker_mul,
    ← mul_kronecker_mul, trace_kronecker, trace_kronecker, hB2, hA2, trace_σz, htrA, htrB]
  norm_num
