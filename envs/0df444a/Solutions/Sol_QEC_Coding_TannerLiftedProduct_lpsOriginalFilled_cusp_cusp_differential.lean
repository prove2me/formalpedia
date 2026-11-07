-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_cusp_differential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:08.870212+00:00
-- url     : https://prove2.me/submissions/59d42a53-3e6b-4d19-beb7-43a9115f30e2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_sources_disjoint
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c d : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledCuspChart N d)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledCuspChart N c).symm.trans (lpsOriginalFilledCuspChart N d)
    lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d) (e z) *
      deriv e z = lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z := by
  let := lpsOriginalFilledTopology N
  by_cases hcd : c=d
  · subst d
    have he : (((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledCuspChart N c)) : ℂ→ℂ) =ᶠ[𝓝 z] id := by
      have hn : ∀ᶠ w in 𝓝 z, w∈(lpsOriginalFilledCuspChart N c).target :=
        (lpsOriginalFilledCuspChart N c).open_target.mem_nhds hz.1
      filter_upwards [hn] with w hw
      exact (lpsOriginalFilledCuspChart N c).right_inv hw
    dsimp only
    rw [he.eq_of_nhds,he.deriv_eq,deriv_id,mul_one]
    rfl
  · have hd := lpsOriginalFilledCuspPartialEquiv_sources_disjoint N
      (lpsOriginalCuspRepresentative N c) (lpsOriginalCuspRepresentative N d)
      (by simpa only [lpsOriginalCuspRepresentative_orbit] using hcd)
    exact False.elim (Set.disjoint_left.mp hd
      ((lpsOriginalFilledCuspChart N c).map_target hz.1) hz.2)
end QEC.Coding.TannerLiftedProduct
