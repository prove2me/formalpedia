-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspOrbit_eq_iff_original_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:12.860984+00:00
-- url     : https://prove2.me/submissions/8ddefbd8-b35c-4cbe-8574-5af0ae50bcd8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspOrbit_eq_of_original_cusp_action
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
    (ρ ρ' : SL(2,ℤ)) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' ↔
      ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ' • (OnePoint.infty : OnePoint ℝ))=
          Matrix.SpecialLinearGroup.mapGL ℝ ρ • (OnePoint.infty : OnePoint ℝ) := by
  constructor
  · intro he
    unfold lpsOriginalCuspOrbit at he
    rw [cosetToCuspOrbit_apply_mk,cosetToCuspOrbit_apply_mk] at he
    have ho := Quotient.eq.mp he
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
    obtain ⟨g,hg⟩ := ho
    refine ⟨g.val,g.property,?_⟩
    have hv := congrArg Subtype.val hg
    simpa only [SubMulAction.val_smul,MulAction.subgroup_smul_def,inv_inv] using hv
  · rintro ⟨g,hg,he⟩
    exact lpsOriginalCuspOrbit_eq_of_original_cusp_action N ρ ρ' g hg he
end QEC.Coding.TannerLiftedProduct
