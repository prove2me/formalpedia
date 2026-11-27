-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:44.973154+00:00
-- url     : https://prove2.me/submissions/e785d5d7-56a7-49f1-962f-c43ea1b77649

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_exists_unitary_diagonal_unitary__1eeef30a6737
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_eval_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_actZ_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_eval_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_eval_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution : Ext := by
  intro ι A B _ _ _ _ p hp g h hgh
  apply MvPolynomial.funext
  intro z
  have hg : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_right_inverse hgh)
  obtain ⟨u₁, u₂, a, hu₁, hu₂, hfac⟩ := exists_unitary_diagonal_unitary' g hg
  have hcancel : ∀ {P Q : Matrix ι ι ℂ} (X : Matrix ι ι ℂ), P * Q = 1 → P * (Q * X) = X := by
    intro P Q X hPQ
    rw [← mul_assoc, hPQ, one_mul]
  have hu1s : u₁ * u₁ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu₁
  have hu2s : u₂ * u₂ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu₂
  have hDD : diagonal (fun i => cexp (a i)) * diagonal (fun i => cexp (-(a i : ℂ))) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hK : g * (u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ) = 1 := by
    rw [hfac]
    simp only [mul_assoc]
    rw [hcancel _ hu2s, hcancel _ hDD, hu1s]
  have hT : hᵀ = u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ := by
    have h1 : hᵀ * g = 1 := _root_.mul_eq_one_comm.mp hgh
    calc hᵀ = hᵀ * (g * (u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ)) := by rw [hK, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hct : ∀ M : Matrix ι ι ℂ, Mᴴᵀ = M.map star := by
    intro M
    ext i j
    simp
  have hh : h = u₁.map star * diagonal (fun i => cexp (-(a i : ℂ))) * u₂.map star := by
    rw [← Matrix.transpose_transpose h, hT, Matrix.transpose_mul, Matrix.transpose_mul, hct, hct,
      Matrix.diagonal_transpose, mul_assoc]
  rw [eval_sub, hfac, hh, actZ_mul, actZ_mul, eval_inv p hp u₁ hu₁, eval_diag p hp a,
    eval_inv p hp u₂ hu₂]
end PositivityTheory.Rg.Sw.FFTSteps
