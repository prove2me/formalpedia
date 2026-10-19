-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.logarithmic_negativity_additive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:09:15.122653+00:00
-- url     : https://prove2.me/submissions/94089a82-3973-4e7a-8029-d5d26a738637

import Mathlib
import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P07
open Entanglement

/-- Eq. (11), PDF p. 3: tensor factors are regrouped by party. -/
theorem gq_dummy_add : True := trivial

open scoped MatrixOrder in
theorem gq_tn {ι : Type*} [Fintype ι] [DecidableEq ι] (M S : Matrix ι ι ℂ) (hS : S.PosSemidef)
    (h : Mᴴ * M = S * S) : traceNorm M = S.trace.re := by
  unfold traceNorm
  rw [h]
  have h0 : (0 : Matrix ι ι ℂ) ≤ S := hS.nonneg
  have h1 : (0 : Matrix ι ι ℂ) ≤ S * S := by
    have := Matrix.posSemidef_conjTranspose_mul_self S
    rw [hS.isHermitian.eq] at this
    exact this.nonneg
  rw [← cfcₙ_eq_cfc, ← CFC.sqrt_eq_real_sqrt _ h1, CFC.sqrt_mul_self S h0]

open scoped MatrixOrder in
theorem gq_sqrt_exists {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ∃ S : Matrix ι ι ℂ, S.PosSemidef ∧ Mᴴ * M = S * S := by
  have h1 : (0 : Matrix ι ι ℂ) ≤ Mᴴ * M := (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  exact ⟨CFC.sqrt (Mᴴ * M), Matrix.LE.le.posSemidef (CFC.sqrt_nonneg _), (CFC.sqrt_mul_sqrt_self _ h1).symm⟩

theorem gq_tn_ne {ι : Type*} [Fintype ι] [DecidableEq ι] (M S : Matrix ι ι ℂ) (hS : S.PosSemidef)
    (h : Mᴴ * M = S * S) (hM : M ≠ 0) : S.trace.re ≠ 0 := by
  intro h0
  have ht : S.trace = 0 := by
    have hn := hS.trace_nonneg
    apply Complex.ext
    · simpa using h0
    · simpa using ((Complex.nonneg_iff.mp hn).2).symm
  rw [hS.trace_eq_zero_iff] at ht
  rw [ht, mul_zero, Matrix.conjTranspose_mul_self_eq_zero] at h
  exact hM h

theorem gq_trace_re {ι : Type*} [Fintype ι] (S : Matrix ι ι ℂ) (hS : S.PosSemidef) :
    S.trace = ((S.trace.re : ℝ) : ℂ) := by
  have hn := hS.trace_nonneg
  apply Complex.ext
  · simp
  · simpa using ((Complex.nonneg_iff.mp hn).2).symm

theorem gq_pt_ne {I J : Type*} [Fintype I] [Fintype J] (rho : Matrix (I × J) (I × J) ℂ)
    (h : rho.trace = 1) : partialTransposeFirst rho ≠ 0 := by
  intro h0
  have : (partialTransposeFirst rho).trace = rho.trace := by
    simp [Matrix.trace, partialTransposeFirst]
  rw [h0, h] at this
  simp at this

theorem solution {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    (rho : Matrix (I × J) (I × J) ℂ) (sigma : Matrix (K × L) (K × L) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    logNeg (bipartiteTensor rho sigma) = logNeg rho+logNeg sigma := by
  obtain ⟨S, hS, hSM⟩ := gq_sqrt_exists (partialTransposeFirst rho)
  obtain ⟨T, hT, hTM⟩ := gq_sqrt_exists (partialTransposeFirst sigma)
  let e := Equiv.prodProdProdComm I K J L
  have hPT : partialTransposeFirst (bipartiteTensor rho sigma) =
      (Matrix.kronecker (partialTransposeFirst rho) (partialTransposeFirst sigma)).submatrix e e := by
    ext p q; rfl
  have hST : ((Matrix.kronecker S T).submatrix e e).PosSemidef := (hS.kronecker hT).submatrix _
  have hmul : (partialTransposeFirst (bipartiteTensor rho sigma))ᴴ * partialTransposeFirst (bipartiteTensor rho sigma) =
      (Matrix.kronecker S T).submatrix e e * (Matrix.kronecker S T).submatrix e e := by
    rw [hPT, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    congr 1
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hSM, hTM]
  have htr : ((Matrix.kronecker S T).submatrix e e).trace = S.trace * T.trace := by
    rw [← Matrix.trace_kronecker]
    unfold Matrix.trace
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold logNeg
  rw [gq_tn _ _ hST hmul, gq_tn _ _ hS hSM, gq_tn _ _ hT hTM, htr, gq_trace_re S hS, gq_trace_re T hT]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact Real.logb_mul (gq_tn_ne _ _ hS hSM (gq_pt_ne rho hrho.2)) (gq_tn_ne _ _ hT hTM (gq_pt_ne sigma hsigma.2))

