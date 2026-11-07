-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_differential_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:53:05.975548+00:00
-- url     : https://prove2.me/submissions/ac9b90ec-33a8-4215-ae0c-2e045db6c81b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_eventually_original_mobius
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsMobius_deriv_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_Gamma0
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwo_slash_deriv
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    let Φ : ℂ→ℂ := fun z => lpsOriginalFilledCuspPartialEquiv N ρ
      (Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))
    lpsOriginalCuspQCoefficient N f ρ (Φ τ) * deriv Φ τ = f τ := by
  obtain ⟨g,hd,hΓ,he⟩ :=
    lpsOriginalCuspCoordinate_eventually_original_mobius N ρ τ hx
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let h := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  let b : ℂ→ℂ := fun z => (g • UpperHalfPlane.ofComplex z : ℍ)
  have hg : 0<g.val.det := by rw [hd];norm_num
  have hr : 0<r.val.det := by
    simp only [r,←Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.det_mapGL,Units.val_one,zero_lt_one]
  have hc := deriv_comp (τ:ℂ)
    ((Function.Periodic.differentiable_qParam (h:=h)).differentiableAt (x:=b τ))
    ((UpperHalfPlane.hasStrictDerivAt_smul hg τ).hasDerivAt.differentiableAt)
  dsimp only
  rw [he.eq_of_nhds,he.deriv_eq]
  simp only [UpperHalfPlane.ofComplex_apply]
  change lpsOriginalCuspQCoefficient N f ρ (Function.Periodic.qParam h ((g • τ : ℍ) : ℂ)) *
    deriv (Function.Periodic.qParam h ∘ b) τ = _
  rw [hc]
  simp only [b,UpperHalfPlane.ofComplex_apply]
  rw [lpsOriginalCuspQCoefficient_pullback,
    lpsWeightTwo_slash_deriv f r hr]
  rw [mul_assoc,←lpsMobius_deriv_mul r g hr hg τ,←mul_smul]
  have ht := lpsCuspDifferential_Gamma0 N f (r*g) hΓ τ 1
  simpa only [lpsCuspDifferential_apply,mul_one] using ht
end QEC.Coding.TannerLiftedProduct
