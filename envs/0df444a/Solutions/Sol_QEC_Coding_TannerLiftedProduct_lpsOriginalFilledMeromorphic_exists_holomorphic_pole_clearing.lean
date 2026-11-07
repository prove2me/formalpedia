-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:50.145466+00:00
-- url     : https://prove2.me/submissions/cc3a1523-3cab-49c1-94b6-354eec12e6b8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_projection_contMDiff
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
    ∃ P : Polynomial ℂ, P.Monic ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ =>
        P.eval (lpsOriginalJInvariant τ) * F (Sum.inl (Quotient.mk
          (MulAction.orbitRel
            (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ))) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  obtain ⟨P,hP,hclear⟩ :=
    lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial N hN F hF
  refine ⟨P,hP,?_⟩
  intro τ
  let π : ℍ → LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk
    (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
  let G : LPSOriginalFilledCurve N → ℂ := fun x => P.eval (lpsOriginalFilledJ N x) * F x
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω G (π τ) := by
    apply contMDiffAt_iff_source.mpr
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    have hchart : chartAt ℂ (π τ) =
        lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ) := rfl
    simpa only [extChartAt_coe_symm,extChartAt_coe,hchart,
      modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Set.range_id,Function.comp_def,id_eq,π,G]
      using (hclear (Quotient.mk _ τ)).contDiffAt.contDiffWithinAt
  have hproj : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω π τ :=
    lpsOriginalFilled_projection_contMDiff N hN τ
  have h := (hg.comp τ hproj).mdifferentiableAt (by decide)
  simpa only [Function.comp_def,G,π,lpsOriginalFilledJ_projection] using h
end QEC.Coding.TannerLiftedProduct
