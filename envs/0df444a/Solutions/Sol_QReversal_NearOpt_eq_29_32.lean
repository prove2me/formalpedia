-- Prove2me | solution 1 for QReversal.NearOpt.eq_29_32
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:12:42.675094+00:00
-- url     : https://prove2.me/submissions/bab73a5b-0d48-48cb-af6b-3cbda6ba9618

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

noncomputable section
namespace QReversal.NearOpt.TraceBoundProof

lemma density_trace_bound {n : Type*} [Fintype n]
    (ρ T : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) :
    Complex.normSq (T * ρ).trace ≤ (T * ρ * Tᴴ).trace.re := by
  classical
  let := Matrix.toMatrixSeminormedAddCommGroup ρ hρ.1
  let := Matrix.toMatrixInnerProductSpace ρ hρ.1
  have h := @inner_mul_inner_self_le ℂ (Matrix n n ℂ) _ _ _ (1 : Matrix n n ℂ) T
  change ‖(T * ρ * (1 : Matrix n n ℂ)ᴴ).trace‖ *
      ‖((1 : Matrix n n ℂ) * ρ * Tᴴ).trace‖ ≤
    ((1 : Matrix n n ℂ) * ρ * (1 : Matrix n n ℂ)ᴴ).trace.re *
      (T * ρ * Tᴴ).trace.re at h
  have heq : (ρ * Tᴴ).trace = star (T * ρ).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hρ.1.isHermitian.eq]
  rw [Complex.normSq_eq_norm_sq, pow_two]
  simpa [heq, hρ.2] using h

lemma trace_sandwich_nonneg {n : Type*} [Fintype n]
    (ρ T : Matrix n n ℂ) (hρ : ρ.PosSemidef) : 0 ≤ (T * ρ * Tᴴ).trace.re :=
  (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same T).trace_nonneg).1

lemma Fe_le_trace_update {n κ : Type*} [Fintype n] [Fintype κ]
    (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (K : κ → Matrix n n ℂ) :
    Fe ρ K ≤ (krausUpdate K ρ).trace.re := by
  simpa only [Fe, krausUpdate, Matrix.trace_sum, Complex.re_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun k _ => density_trace_bound ρ (K k) hρ)

lemma Fbar_le_weighted_trace {n κ L : Type*} [Fintype n] [Fintype κ] [Fintype L]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (ρs : L → Matrix n n ℂ)
    (hρs : ∀ l, IsDensityMatrix (ρs l)) (K : κ → Matrix n n ℂ) :
    Fbar p ρs K ≤ ∑ l, p l * (krausUpdate K (ρs l)).trace.re := by
  exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
    (Fe_le_trace_update (ρs l) (hρs l) K) (hp l)

end QReversal.NearOpt.TraceBoundProof


open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder
open QReversal.NearOpt QReversal.NearOpt.TraceBoundProof

noncomputable section

theorem solution {n L κ : Type*} [Fintype n] [Fintype L] [Fintype κ]
    (p : L → ℝ) (hp : ∀ l, 0 ≤ p l) (ρs : L → Matrix n n ℂ)
    (hρs : ∀ l, IsDensityMatrix (ρs l))
    (Rl Bl : L → κ → Matrix n n ℂ) :
    ∑ l, p l * ∑ i, Complex.normSq (Matrix.trace (ρs l * Rl l i * Bl l i)) ≤
      ∑ l, p l * ∑ i, ∑ j,
        (Matrix.trace (Rl l i * Bl l j * ρs l * (Bl l j)ᴴ * (Rl l i)ᴴ)).re := by
  classical
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ (hp l)
  apply Finset.sum_le_sum
  intro i _
  have hc : (ρs l * Rl l i * Bl l i).trace = (Rl l i * Bl l i * ρs l).trace := by
    rw [mul_assoc, Matrix.trace_mul_comm]
  calc
    _ ≤ (Rl l i * Bl l i * ρs l * (Bl l i)ᴴ * (Rl l i)ᴴ).trace.re := by
      rw [hc]
      simpa only [conjTranspose_mul, mul_assoc] using
        density_trace_bound (ρs l) (Rl l i * Bl l i) (hρs l)
    _ ≤ _ := Finset.single_le_sum
      (f := fun j : κ => (Rl l i * Bl l j * ρs l * (Bl l j)ᴴ * (Rl l i)ᴴ).trace.re)
      (fun j _ => by
      simpa only [conjTranspose_mul, mul_assoc] using
        trace_sandwich_nonneg (ρs l) (Rl l i * Bl l j) (hρs l).1) (Finset.mem_univ i)
