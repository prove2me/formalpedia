-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_modular_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:51:32.605202+00:00
-- url     : https://prove2.me/submissions/89aa90c8-2119-41d0-92ea-74783e4e244f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_modular_numerator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicDeltaPowerAtLevel_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomial_exists_nonzero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_polynomial
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ (k : ℕ)
      (A B : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        ((k : ℤ)*12)), B ≠ 0 ∧ ∀ τ : ℍ,
      A τ = B τ * F (Sum.inl ⟦τ⟧) := by
  obtain ⟨P,a,A,hP,hA⟩ :=
    lpsOriginalFilledMeromorphic_exists_modular_numerator N hN F hF
  let J : LPSOriginalFilledCurve N → ℂ := fun x => P.eval (lpsOriginalFilledJ N x)
  have hJ : lpsOriginalFilledChartMeromorphic N hN J :=
    lpsOriginalFilledChartMeromorphic_polynomial N hN
      (lpsOriginalFilledChartMeromorphic_j N hN) P
  obtain ⟨b,hb⟩ := lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded N hN J hJ
  have hjhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => J (Sum.inl ⟦τ⟧)) := by
    have hh := (lpsOriginalJHolomorphicEval P).property
    have he : (lpsOriginalJHolomorphicEval P).val = (fun τ : ℍ => J (Sum.inl ⟦τ⟧)) := by
      funext τ
      exact lpsOriginalJHolomorphicEval_apply P τ
    rw [he] at hh
    exact hh
  let B := lpsOriginalFilledFunctionDeltaModularForm N J b hjhol hb
  let K := a+b
  have hwa : (a : ℤ)*12+(b : ℤ)*12=(K : ℤ)*12 := by
    simp only [K,Nat.cast_add,add_mul]
  have hwb : (b : ℤ)*12+(a : ℤ)*12=(K : ℤ)*12 := by
    simp only [K,Nat.cast_add,add_mul]
    ring
  let A' := (A.mul (lpsOriginalMeromorphicDeltaPowerAtLevel N b)).mcast hwa
  let B' := (B.mul (lpsOriginalMeromorphicDeltaPowerAtLevel N a)).mcast hwb
  have hAval (τ : ℍ) : A' τ = ModularForm.discriminant τ ^ K *
      P.eval (lpsOriginalJInvariant τ) * F (Sum.inl ⟦τ⟧) := by
    dsimp only [A']
    rw [ModularForm.mcast_apply,ModularForm.coe_mul,Pi.mul_apply,hA,
      lpsOriginalMeromorphicDeltaPowerAtLevel_apply]
    dsimp only [K]
    rw [pow_add]
    ring
  have hBval (τ : ℍ) : B' τ = ModularForm.discriminant τ ^ K *
      P.eval (lpsOriginalJInvariant τ) := by
    dsimp only [B']
    rw [ModularForm.mcast_apply,ModularForm.coe_mul,Pi.mul_apply,
      lpsOriginalMeromorphicDeltaPowerAtLevel_apply]
    change (ModularForm.discriminant τ ^ b * P.eval (lpsOriginalJInvariant τ)) *
      ModularForm.discriminant τ ^ a = _
    dsimp only [K]
    rw [pow_add]
    ring
  refine ⟨K,A',B',?_,?_⟩
  · obtain ⟨τ,hτ⟩ := lpsOriginalJPolynomial_exists_nonzero P hP.ne_zero
    intro hzero
    have hh := congrArg (fun f => f τ) hzero
    rw [hBval] at hh
    exact (mul_ne_zero (pow_ne_zero K (ModularForm.discriminant_ne_zero τ)) hτ) hh
  · intro τ
    rw [hAval,hBval]
end QEC.Coding.TannerLiftedProduct
