-- Prove2me | solution 1 for OCB2012.protocol_pSucc
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:16:10.742445+00:00
-- url     : https://prove2.me/submissions/076af27b-0528-4c15-848a-71930ab35032

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_OCB2012_eq26_and_alice_guess

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

lemma σz_mul_σz : σz * σz = 1 := by
  rw [σz, mul_fin_two, one_fin_two]; norm_num

lemma σx_mul_σx : σx * σx = 1 := by
  rw [σx, mul_fin_two, one_fin_two]; norm_num

lemma σz_herm : σzᴴ = σz := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σz]

lemma σx_herm : σxᴴ = σx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σx]

lemma star_sgn (x : Bool) : star (sgn x) = sgn x := by cases x <;> simp [sgn]

lemma sgn_mul_self (x : Bool) : sgn x * sgn x = 1 := by cases x <;> simp [sgn]

/-- `𝟙 + U` is positive semidefinite for a Hermitian involution `U`. -/
lemma posSemidef_one_add {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : Uᴴ = U) (hUU : U * U = 1) : (1 + U).PosSemidef := by
  have h : 1 + U = (1 / 2 : ℂ) • ((1 + U)ᴴ * (1 + U)) := by
    rw [conjTranspose_add, conjTranspose_one, hU, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      hUU, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    rw [show (1 : Matrix n n ℂ) + U + (U + 1) = (2 : ℂ) • (1 + U) by rw [two_smul]; abel,
      smul_smul]; norm_num
  rw [h]
  refine (posSemidef_conjTranspose_mul_self _).smul ?_
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_le_real.mpr (by norm_num)

lemma psd_z (x : Bool) : (1 + sgn x • σz).PosSemidef :=
  posSemidef_one_add _ (by rw [conjTranspose_smul, σz_herm, star_sgn])
    (by rw [smul_mul_smul_comm, sgn_mul_self, σz_mul_σz, one_smul])

lemma psd_x (x : Bool) : (1 + sgn x • σx).PosSemidef :=
  posSemidef_one_add _ (by rw [conjTranspose_smul, σx_herm, star_sgn])
    (by rw [smul_mul_smul_comm, sgn_mul_self, σx_mul_σx, one_smul])

lemma nonneg_quarter : (0 : ℂ) ≤ 1 / 4 := by
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_le_real.mpr (by norm_num)

lemma nonneg_half : (0 : ℂ) ≤ 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_le_real.mpr (by norm_num)

lemma ptrace₂_kron {α β : Type*} [Fintype β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    ptrace₂ (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp [ptrace₂, kroneckerMap_apply, trace, Finset.mul_sum, mul_comm]

lemma ptrace₂_add {α β : Type*} [Fintype β] (M N : Matrix (α × β) (α × β) ℂ) :
    ptrace₂ (M + N) = ptrace₂ M + ptrace₂ N := by
  ext i j; simp [ptrace₂, Finset.sum_add_distrib]

lemma ptrace₂_smul {α β : Type*} [Fintype β] (r : ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    ptrace₂ (r • M) = r • ptrace₂ M := by
  ext i j; simp [ptrace₂, Finset.mul_sum]

lemma tr_1z (s : ℂ) : (1 + s • σz).trace = 2 := by
  simp [σz, trace_fin_two]

lemma tr_1x (s : ℂ) : (1 + s • σx).trace = 2 := by
  simp [σx, trace_fin_two]

lemma ξ_instrument : IsAliceInstrument ξ := by
  refine ⟨fun x a => ((psd_z x).kronecker (psd_z a)).smul nonneg_quarter, fun a => ?_⟩
  rw [Fintype.sum_bool]
  refine ⟨(((psd_z true).kronecker (psd_z a)).smul nonneg_quarter).add
    (((psd_z false).kronecker (psd_z a)).smul nonneg_quarter), ?_⟩
  simp only [ξ, ptrace₂_add, ptrace₂_smul, ptrace₂_kron, tr_1z]
  ext i j; fin_cases i <;> fin_cases j <;> simp [σz, sgn] <;> norm_num

lemma η_instrument (ρ : Matrix Qubit Qubit ℂ) (hρ : PeresTerno.IsDensityMatrix ρ) :
    IsBobInstrument (η ρ) := by
  refine ⟨fun y b b' => ?_, fun b b' => ?_⟩
  · cases b'
    · exact ((psd_x y).kronecker (psd_z (xor b y))).smul nonneg_quarter
    · exact ((psd_z y).kronecker hρ.1).smul nonneg_half
  · rw [Fintype.sum_bool]
    cases b'
    · refine ⟨(((psd_x true).kronecker (psd_z (xor b true))).smul nonneg_quarter).add
        (((psd_x false).kronecker (psd_z (xor b false))).smul nonneg_quarter), ?_⟩
      simp only [η, Bool.false_eq_true, if_false, ptrace₂_add, ptrace₂_smul, ptrace₂_kron, tr_1z]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σx, sgn] <;> norm_num
    · refine ⟨(((psd_z true).kronecker hρ.1).smul nonneg_half).add
        (((psd_z false).kronecker hρ.1).smul nonneg_half), ?_⟩
      simp only [η, if_true, ptrace₂_add, ptrace₂_smul, ptrace₂_kron, hρ.2]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σz, sgn] <;> norm_num

end OCB2012Sol

open OCB2012 OCB2012Sol in
theorem solution (ρ : Matrix Qubit Qubit ℂ) (hρ : PeresTerno.IsDensityMatrix ρ) :
    IsAliceInstrument ξ ∧ IsBobInstrument (η ρ) ∧
      pSucc W7 ξ (η ρ) = (2 + Real.sqrt 2) / 4 := by
  refine ⟨ξ_instrument, η_instrument ρ hρ, ?_⟩
  obtain ⟨h1, h0⟩ := eq26_and_alice_guess ρ hρ
  -- Bob's guess (b' = 1): P(y = a | a, b, b' = 1) = ½ (1 + 1/√2)
  have hB : ∀ a b : Bool, ∑ x : Bool, (prob W7 (ξ x a) (η ρ a b true)).re =
      2⁻¹ * (1 + Real.sqrt 2 / 2) := by
    intro a b
    have := congrArg Complex.re (h1 a b a)
    simpa [Complex.re_sum] using this
  -- Alice's guess (b' = 0)
  have hA := congrArg Complex.re h0
  simp only [Fintype.sum_bool, Complex.ofReal_re, Complex.mul_re, Complex.add_re] at hA
  norm_num at hA
  simp only [pSucc, hB]
  simp only [Fintype.sum_bool] at hA ⊢
  linarith
