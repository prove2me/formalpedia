-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapX02.negativity_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:37:39.932458+00:00
-- url     : https://prove2.me/submissions/0f517431-2efd-47b5-bdb6-39ebc72194ee

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
open Matrix QAlgorithms QAlgorithms.Entanglement

private lemma trace_conj_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) (A : Matrix I I ℂ) :
    (U.val * A * star U.val).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  simp

private lemma traceNorm_eq_abs {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : traceNorm A = (CFC.abs A).trace.re := by
  unfold traceNorm CFC.abs
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _ (star_mul_self_nonneg A)]
  have hf : (fun x : ℝ => (NNReal.sqrt x.toNNReal : ℝ)) = Real.sqrt := by
    funext x
    rw [Real.sqrt]
  rw [hf, Matrix.star_eq_conjTranspose]

private lemma trace_abs_spectral {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    (CFC.abs A).trace.re = ∑ i, |hA.eigenvalues i| := by
  rw [CFC.abs_eq_cfc_norm A hA, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [trace_conj_unitary]
  simp [Matrix.trace_diagonal, Function.comp_def]

private lemma trace_abs_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian)
    (hp : (B - A).PosSemidef) (hm : (B + A).PosSemidef) :
    (CFC.abs A).trace.re ≤ B.trace.re := by
  let U := hA.eigenvectorUnitary
  have hd : star (U : Matrix I I ℂ) * A * (U : Matrix I I ℂ) =
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb : (star (U : Matrix I I ℂ) * B * (U : Matrix I I ℂ)).trace = B.trace := by
    simpa only [Unitary.coe_star, star_star] using trace_conj_unitary (star U) B
  rw [trace_abs_spectral A hA, ← hb]
  simp only [Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hpi := (hp.conjTranspose_mul_mul_same (U : Matrix I I ℂ)).diag_nonneg (i := i)
  have hmi := (hm.conjTranspose_mul_mul_same (U : Matrix I I ℂ)).diag_nonneg (i := i)
  rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.star_eq_conjTranspose, hd] at hpi
  rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.star_eq_conjTranspose, hd] at hmi
  have hp' := (Complex.nonneg_iff.mp hpi).1
  have hm' := (Complex.nonneg_iff.mp hmi).1
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply_eq,
    Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hp' hm'
  change |hA.eigenvalues i| ≤ ((star (U : Matrix I I ℂ) * B * (U : Matrix I I ℂ)) i i).re
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma abs_minus_pos {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) : (CFC.abs A - A).PosSemidef := by
  rw [CFC.abs_sub_self A hA]
  exact (show 0 ≤ 2 • negPart A by simpa only [two_smul] using add_nonneg (CFC.negPart_nonneg A) (CFC.negPart_nonneg A)).posSemidef

private lemma abs_plus_pos {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) : (CFC.abs A + A).PosSemidef := by
  rw [CFC.abs_add_self A hA]
  exact (show 0 ≤ 2 • posPart A by simpa only [two_smul] using add_nonneg (CFC.posPart_nonneg A) (CFC.posPart_nonneg A)).posSemidef

private lemma traceNorm_mixture {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k).IsHermitian)
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) :
    traceNorm (∑ k, p k • A k) ≤ ∑ k, p k * traceNorm (A k) := by
  let S := ∑ k, p k • A k
  let B := ∑ k, p k • CFC.abs (A k)
  have hs : S.IsHermitian := by
    apply IsSelfAdjoint.isHermitian
    exact isSelfAdjoint_sum _ fun k _ => (isSelfAdjoint_iff.mpr (show star (p k) = p k from rfl)).smul (hA k).isSelfAdjoint
  have hpos : (B - S).PosSemidef := by
    change (∑ k, p k • CFC.abs (A k) - ∑ k, p k • A k).PosSemidef
    rw [← Finset.sum_sub_distrib]
    apply Matrix.posSemidef_sum
    intro k hk
    simpa only [smul_sub] using (abs_minus_pos (A k) (hA k)).smul (hp k)
  have hneg : (B + S).PosSemidef := by
    change (∑ k, p k • CFC.abs (A k) + ∑ k, p k • A k).PosSemidef
    rw [← Finset.sum_add_distrib]
    apply Matrix.posSemidef_sum
    intro k hk
    simpa only [smul_add] using (abs_plus_pos (A k) (hA k)).smul (hp k)
  rw [traceNorm_eq_abs]
  calc
    _ ≤ B.trace.re := trace_abs_bound S B hs hpos hneg
    _ = _ := by simp [B, Matrix.trace_sum, Matrix.trace_smul, traceNorm_eq_abs]

theorem solution {dA dB count : ℕ} (hA : 0 < dA) (hB : 0 < dB)
    (rho : Fin count → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hermitian : ∀ i, (rho i).IsHermitian)
    (p : Fin count → ℝ) (nonnegative : ∀ i, 0 ≤ p i) (total : ∑ i, p i = 1) :
    QAlgorithms.Entanglement.negativity (∑ i, (p i : ℂ) • rho i) ≤
      ∑ i, p i * QAlgorithms.Entanglement.negativity (rho i) := by
  have hpt i : (partialTransposeFirst (rho i)).IsHermitian := by
    ext x y
    exact congrFun (congrFun (hermitian i) (y.1, x.2)) (x.1, y.2)
  have hlin : partialTransposeFirst (∑ i, (p i : ℂ) • rho i) =
      ∑ i, p i • partialTransposeFirst (rho i) := by
    ext x y
    simp [partialTransposeFirst, Matrix.sum_apply, Complex.real_smul]
  have h := traceNorm_mixture (fun i => partialTransposeFirst (rho i)) hpt p nonnegative
  simp only [Entanglement.negativity, hlin]
  have hr : (∑ i, p i * ((traceNorm (partialTransposeFirst (rho i)) - 1) / 2)) =
      ((∑ i, p i * traceNorm (partialTransposeFirst (rho i))) - 1) / 2 := by
    simp_rw [← mul_div_assoc, mul_sub, mul_one]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, total]
  rw [hr]
  linarith

#print axioms solution
