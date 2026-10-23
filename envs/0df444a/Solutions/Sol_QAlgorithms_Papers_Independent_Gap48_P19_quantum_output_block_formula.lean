-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P19.quantum_output_block_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:37:21.424697+00:00
-- url     : https://prove2.me/submissions/4ffaa991-342b-464e-8a63-f9d8ec00b9e7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

open scoped Matrix ComplexConjugate ComplexOrder
open Matrix

namespace QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_alice_apply {A B : Type} [DecidableEq A] (a : A) (x y : (A × A) × (B × B)) :
    aliceProject (B := B) a x y = if x = y then (if x.1.1 = a then 1 else 0) else 0 := by
  simp only [aliceProject, Matrix.diagonal, Matrix.of_apply]

theorem x8_PM {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (a : A)
    (M : Mat ((A × A) × (B × B))) (x y : (A × A) × (B × B)) :
    (aliceProject (B := B) a * M * aliceProject (B := B) a) x y =
      (if x.1.1 = a then 1 else 0) * (if y.1.1 = a then 1 else 0) * M x y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single y]
  · rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · simp only [x8_alice_apply, if_true]; ring
    · intro k _ hk; rw [x8_alice_apply, if_neg (Ne.symm hk), zero_mul]
    · simp
  · intro k _ hk; rw [x8_alice_apply, if_neg hk, mul_zero]
  · simp

theorem x8_branch_apply {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Mat (A × B)) (U : Matrix.unitaryGroup (A × A) ℂ)
    (V : A → Matrix.unitaryGroup (B × B) ℂ) (a : A) (x y : (A × A) × (B × B)) :
    quantumBranchFull rho sigma U V a x y =
      (if x.1.1 = a then 1 else 0) * (if y.1.1 = a then 1 else 0) *
      ∑ i : (A × A) × (B × B), ∑ j : (A × A) × (B × B),
        (U : Mat (A × A)) x.1 i.1 * (V a : Mat (B × B)) x.2 i.2 *
        rho (i.1.1, i.2.1) (j.1.1, j.2.1) * sigma (i.1.2, i.2.2) (j.1.2, j.2.2) *
        conj ((V a : Mat (B × B)) y.2 j.2) * conj ((U : Mat (A × A)) y.1 j.1) := by
  simp only [quantumBranchFull]
  rw [show ∀ P W X : Mat ((A × A) × (B × B)), P * W * X * Wᴴ * P = P * (W * X * Wᴴ) * P from
    fun P W X => by simp only [Matrix.mul_assoc], x8_PM]
  congr 1
  simp only [Matrix.mul_apply, conjTranspose_apply, inputCopies, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Finset.sum_mul, RCLike.star_def, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem x8_branch_psd {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho sigma : Mat (A × B)) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (U : Matrix.unitaryGroup (A × A) ℂ)
    (V : A → Matrix.unitaryGroup (B × B) ℂ) (a : A) :
    (quantumBranchFull rho sigma U V a).PosSemidef := by
  have hX : (inputCopies rho sigma).PosSemidef := by
    have h := (hrho.kronecker hsigma).submatrix
      (fun i : (A × A) × (B × B) => ((i.1.1, i.2.1), (i.1.2, i.2.2)))
    have e : inputCopies rho sigma = (Matrix.kroneckerMap (· * ·) rho sigma).submatrix
      (fun i : (A × A) × (B × B) => ((i.1.1, i.2.1), (i.1.2, i.2.2)))
      (fun i : (A × A) × (B × B) => ((i.1.1, i.2.1), (i.1.2, i.2.2))) := by
      ext i j; rfl
    rw [e]; exact h
  simp only [quantumBranchFull]
  set W := Matrix.kronecker (U : Mat (A × A)) (V a : Mat (B × B))
  set P := aliceProject (B := B) a
  have hP : Pᴴ = P := by
    ext x y
    rw [conjTranspose_apply]
    simp only [P]
    rw [x8_alice_apply, x8_alice_apply]
    by_cases h : x = y
    · subst h; split_ifs <;> simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  have h1 := hX.conjTranspose_mul_mul_same Wᴴ
  rw [conjTranspose_conjTranspose] at h1
  have h2 := h1.conjTranspose_mul_mul_same P
  rw [hP] at h2
  simpa only [Matrix.mul_assoc] using h2

theorem x8_main {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Mat (A × B)) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (U : Matrix.unitaryGroup (A × A) ℂ) (V : A → Matrix.unitaryGroup (B × B) ℂ)
    (a0 : A) (b0 : B) (hsuccess : 0 < quantumSuccess rho sigma U V a0 b0) :
    IsDensityMatrix (measuredSelectionOutput rho sigma U V a0 b0) ∧
    (∀ a b1 b2, measuredSelectionOutput rho sigma U V a0 b0 (a, b1) (a, b2) =
      quantumBlock rho sigma U V a0 b0 a b1 b2) ∧
    (∀ a1 a2 b1 b2, a1 ≠ a2 →
      measuredSelectionOutput rho sigma U V a0 b0 (a1, b1) (a2, b2) = 0) := by
  set s := quantumSuccess rho sigma U V a0 b0
  set N := quantumNumerator rho sigma U V a0 b0
  have hN : N = ∑ a, (quantumBranchFull rho sigma U V a).submatrix
      (fun i : A × B => ((i.1, a0), (i.2, b0))) (fun i : A × B => ((i.1, a0), (i.2, b0))) := by
    ext i j
    simp only [N, quantumNumerator, Matrix.sum_apply, Matrix.submatrix_apply]
  have hNpsd : N.PosSemidef := by
    rw [hN]
    exact posSemidef_sum _ (fun a _ => (x8_branch_psd rho sigma hrho.1 hsigma.1 U V a).submatrix _)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [measuredSelectionOutput]
    have hs : (0 : ℂ) ≤ ((s⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.2 (inv_nonneg.2 hsuccess.le)
    have := hNpsd.smul hs
    convert this using 2
    push_cast; rfl
  · simp only [measuredSelectionOutput, trace_smul, smul_eq_mul]
    have htr : N.trace = (s : ℂ) := by
      have h0 := hNpsd.trace_nonneg
      apply Complex.ext
      · rfl
      · simp only [Complex.ofReal_im]
        exact ((Complex.nonneg_iff.1 h0).2).symm
    change ((s)⁻¹ : ℂ) * N.trace = 1
    rw [htr]
    exact inv_mul_cancel₀ (by exact_mod_cast hsuccess.ne')
  · intro a b1 b2
    simp only [measuredSelectionOutput, quantumBlock, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp only [quantumNumerator, x8_branch_apply]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  · intro a1 a2 b1 b2 h
    simp only [measuredSelectionOutput, Matrix.smul_apply, smul_eq_mul]
    simp only [quantumNumerator, x8_branch_apply]
    rw [Finset.sum_eq_zero, mul_zero]
    intro c _
    by_cases h1 : a1 = c
    · subst h1; rw [if_neg (Ne.symm h)]; simp
    · rw [if_neg h1]; simp

end

end QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms.Papers.Independent.Gap48.P19 in
open QAlgorithms.Papers.Independent.Information100.P75 (Mat) in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Mat (A × B)) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (U : Matrix.unitaryGroup (A × A) ℂ) (V : A → Matrix.unitaryGroup (B × B) ℂ)
    (a0 : A) (b0 : B) (hsuccess : 0 < quantumSuccess rho sigma U V a0 b0) :
    QAlgorithms.IsDensityMatrix (measuredSelectionOutput rho sigma U V a0 b0) ∧
    (∀ a b1 b2, measuredSelectionOutput rho sigma U V a0 b0 (a, b1) (a, b2) =
      quantumBlock rho sigma U V a0 b0 a b1 b2) ∧
    (∀ a1 a2 b1 b2, a1 ≠ a2 →
      measuredSelectionOutput rho sigma U V a0 b0 (a1, b1) (a2, b2) = 0) :=
  x8_main rho sigma hrho hsigma U V a0 b0 hsuccess
