-- Prove2me | solution 1 for VectorCalculus.conservative_partialDeriv_symm
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:29:40.15493+00:00
-- url     : https://prove2.me/submissions/54c592d5-2a3e-406b-bab3-45884dba4a79

import Mathlib
import Definitions.Def_VectorCalculus_grad

namespace SymmAux
open VectorCalculus

lemma partialDeriv_eq {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : Differentiable ℝ φ) (y : Fin n → ℝ)
    (i : Fin n) : partialDeriv φ i y = fderiv ℝ φ y (Pi.single i 1) := by
  unfold partialDeriv
  have hf := hasDerivAt_update y i (y i)
  have hl : HasFDerivAt φ (fderiv ℝ φ y) (Function.update y i (y i)) := by
    rw [Function.update_eq_self]; exact (hφ y).hasFDerivAt
  exact (hl.comp_hasDerivAt (y i) hf).deriv

end SymmAux
open VectorCalculus SymmAux

theorem solution {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (hFφ : ∀ y, F y = grad φ y)
    (i j : Fin n) (y : Fin n → ℝ) :
    partialDeriv (fun z => F z j) i y = partialDeriv (fun z => F z i) j y := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ φ) := hD.differentiable (by norm_num)
  have hF : ∀ k, (fun z => F z k) = fun z => fderiv ℝ φ z (Pi.single k 1) := by
    intro k; funext z; rw [hFφ, grad, partialDeriv_eq φ hφd]
  have hgd : ∀ k, Differentiable ℝ (fun z => fderiv ℝ φ z (Pi.single k 1)) :=
    fun k => hDd.clm_apply (differentiable_const _)
  have hsecond : ∀ k l, partialDeriv (fun z => fderiv ℝ φ z (Pi.single k 1)) l y =
      fderiv ℝ (fderiv ℝ φ) y (Pi.single l 1) (Pi.single k 1) := by
    intro k l
    rw [partialDeriv_eq _ (hgd k), fderiv_clm_apply (hDd y) (differentiableAt_const _)]
    simp
  rw [hF j, hF i, hsecond, hsecond]
  have hsymm := (hφ.contDiffAt (x := y)).isSymmSndFDerivAt (by simp [minSmoothness])
  exact hsymm _ _
