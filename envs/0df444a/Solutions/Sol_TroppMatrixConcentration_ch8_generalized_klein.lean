-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_generalized_klein
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:44:27.494983+00:00
-- url     : https://prove2.me/submissions/d4bb3e87-2b28-417c-b0df-f9e563219a0c

import Definitions.Def_TroppMatrixConcentration_ch8_entropy
import Mathlib.Tactic.Ring
open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix
set_option autoImplicit false
private theorem trace_pair {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℝ) :
    (trace ((U * diagonal (fun j => (a j : ℂ)) * Uᴴ) *
      (V * diagonal (fun k => (b k : ℂ)) * Vᴴ))).re =
    ∑ j, ∑ k, a j * b k * Complex.normSq ((Uᴴ * V) j k) := by
  let W := Uᴴ * V
  have hw : Vᴴ * U = Wᴴ := by simp [W, conjTranspose_mul]
  calc
    _ = (trace (diagonal (fun j => (a j : ℂ)) * W *
       diagonal (fun k => (b k : ℂ)) * Wᴴ)).re := by
      simp only [W, ← hw]
      congr 1
      simp only [mul_assoc]
      rw [trace_mul_comm U]
      simp only [mul_assoc]
    _ = _ := by
      change (trace (diagonal (fun j => (a j : ℂ)) * W *
        diagonal (fun k => (b k : ℂ)) * Wᴴ)).re = ∑ j, ∑ k, a j * b k * Complex.normSq (W j k)
      simp only [trace, diag_apply]
      simp only [mul_apply, diagonal, of_apply, ite_mul, mul_ite, zero_mul, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, conjTranspose_apply, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
      <;> ring

open TroppMatrixConcentration

theorem solution {d N : ℕ} [NeZero d]
    (I : Set ℝ) (hI : Convex ℝ I) (f g : Fin N → ℝ → ℝ)
    (hfg : ∀ a ∈ I, ∀ h ∈ I, 0 ≤ ∑ i, f i a * g i h)
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hHI : spectrum ℝ H ⊆ I) :
    0 ≤ ∑ i, (Matrix.trace (ch8_matrixFunction (f i) A *
      ch8_matrixFunction (g i) H)).re := by
  have heq (i : Fin N) :
      (trace (ch8_matrixFunction (f i) A * ch8_matrixFunction (g i) H)).re =
      ∑ j, ∑ k, f i (hA.eigenvalues j) * g i (hH.eigenvalues k) *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
          (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) j k) := by
    simp only [ch8_matrixFunction, hA.cfc_eq, hH.cfc_eq, Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]
    exact trace_pair _ _ _ _
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro k _
  rw [← Finset.sum_mul]
  exact mul_nonneg (hfg _ (hAI (hA.eigenvalues_mem_spectrum_real j)) _
    (hHI (hH.eigenvalues_mem_spectrum_real k))) (Complex.normSq_nonneg _)
