-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspOrbit_eq_of_original_cusp_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:20.393089+00:00
-- url     : https://prove2.me/submissions/b618274f-6d9f-4eab-87b9-411846b8faee

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (he : g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ' • (OnePoint.infty : OnePoint ℝ))=
      Matrix.SpecialLinearGroup.mapGL ℝ ρ • (OnePoint.infty : OnePoint ℝ)) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' := by
  unfold lpsOriginalCuspOrbit
  rw [cosetToCuspOrbit_apply_mk,cosetToCuspOrbit_apply_mk]
  apply Quotient.eq.mpr
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  refine ⟨⟨g,hg⟩,?_⟩
  apply Subtype.ext
  simpa only [SubMulAction.val_smul,MulAction.subgroup_smul_def,inv_inv] using he
end QEC.Coding.TannerLiftedProduct
