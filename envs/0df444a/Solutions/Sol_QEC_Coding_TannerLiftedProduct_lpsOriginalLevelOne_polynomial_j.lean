-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelOne_polynomial_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:41:59.700253+00:00
-- url     : https://prove2.me/submissions/b7c848d5-3f26-4dbe-979e-30b1021cb462

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubePower_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubePower_qconstant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDelta_j_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) :
    ∃ P : Polynomial ℂ, P.natDegree≤m ∧ ∀ τ : ℍ,
      f τ=ModularForm.discriminant τ^m*P.eval (lpsOriginalJInvariant τ) := by
  induction m with
  | zero =>
    let g : ModularForm 𝒮ℒ 0 := ModularForm.mcast (by norm_num) f
    obtain ⟨c,hc⟩ := ModularFormClass.levelOne_weight_zero_const g
    refine ⟨Polynomial.C c,by simp,?_⟩
    intro τ
    have h := congr_fun hc τ
    simpa only [g,ModularForm.mcast_apply,Function.const_apply,pow_zero,
      Polynomial.eval_C,one_mul] using h
  | succ m ih =>
    let g := lpsOriginalE4CubePower (m+1)
    let c := (qExpansion 1 f).coeff 0
    obtain ⟨h,hh⟩ := ModularForm.sub_smul_isCuspForm f g
      (lpsOriginalE4CubePower_qconstant (m+1))
    let d : ModularForm 𝒮ℒ (12*(m:ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (CuspForm.discriminantEquiv h)
    obtain ⟨P,hP,hPeval⟩ := ih d
    refine ⟨P+Polynomial.C c*Polynomial.X^(m+1),
      Polynomial.natDegree_add_le_of_degree_le (hP.trans (Nat.le_succ m))
        (Polynomial.natDegree_C_mul_X_pow_le c (m+1)),?_⟩
    intro τ
    have hΔ : ModularForm.discriminant τ*d τ=h τ :=
      ModularForm.discriminant_mul_discriminantEquiv_apply h τ
    have hv : h τ=f τ-c*g τ := congrArg (fun u : ModularForm 𝒮ℒ (12*((m+1:ℕ):ℤ)) => u τ) hh
    rw [hPeval τ] at hΔ
    have hg : g τ=(ModularForm.E₄ τ^3)^(m+1) :=
      lpsOriginalE4CubePower_apply (m+1) τ
    rw [hg] at hv
    rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X]
    have hp := lpsOriginalDelta_j_power (m+1) τ
    rw [pow_succ] at hp ⊢
    linear_combination -hΔ-hv-c*hp
end QEC.Coding.TannerLiftedProduct
