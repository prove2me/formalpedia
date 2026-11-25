-- Prove2me | solution 1 for ReciprocityTheory.AnForm.vecMul_hessC_comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:35.084796+00:00
-- url     : https://prove2.me/submissions/64cbc1ff-8d6e-442d-9889-cc669b3523e9

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Theorems.Thm_ReciprocityTheory_AnForm_hessC_eq_leviC
import Theorems.Thm_ReciprocityTheory_AnForm_sum_mul_leviC
import Theorems.Thm_ReciprocityTheory_AnForm_hess_comp_of_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Complex Filter Topology
open scoped Matrix
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (v : Fin e → ℂ) (hv : fderiv ℂ τ z v = 0) :
    v ᵥ* hessC (φ ∘ τ) z = 0 := by
  have hH : ∀ b, leviC (fderiv ℝ (fderiv ℝ (φ ∘ τ)) z) v b = 0 := by
    intro b
    have hIv : fderiv ℂ τ z (Complex.I • v) = 0 := by rw [map_smul, hv, smul_zero]
    have hdiff : DifferentiableAt ℂ (fun x => fderiv ℂ τ x b) z :=
      (hτ.fderiv.differentiableAt).clm_apply (differentiableAt_const b)
    have hB : fderiv ℂ (fun x => fderiv ℂ τ x (Complex.I • b)) z =
        Complex.I • fderiv ℂ (fun x => fderiv ℂ τ x b) z := by
      have h0 : (fun x => fderiv ℂ τ x (Complex.I • b)) = fun x => Complex.I • fderiv ℂ τ x b := by
        funext x
        rw [map_smul]
      rw [h0]
      exact fderiv_const_smul hdiff Complex.I
    unfold leviC
    rw [hess_comp_of_ker φ τ z hτ hφ v b hv, hess_comp_of_ker φ τ z hτ hφ v _ hv,
      hess_comp_of_ker φ τ z hτ hφ _ b hIv, hess_comp_of_ker φ τ z hτ hφ _ _ hIv, hB]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
      map_neg]
    simp
  funext j
  show ∑ i, v i * hessC (φ ∘ τ) z i j = 0
  simp_rw [hessC_eq_leviC]
  rw [sum_mul_leviC, hH]
end ReciprocityTheory.AnForm
