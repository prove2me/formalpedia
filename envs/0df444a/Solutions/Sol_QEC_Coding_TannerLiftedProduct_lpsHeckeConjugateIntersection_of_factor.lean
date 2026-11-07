-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:29.886664+00:00
-- url     : https://prove2.me/submissions/00a31f42-5710-4b58-a370-b875e4e723e3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_mem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (γ δ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (he : lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) *
        Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ *
        lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) :
    γ ∈ lpsHeckeConjugateIntersection N p := by
  rw [lpsHeckeConjugateIntersection_mem]
  refine ⟨hγ,δ 0 1,?_⟩
  have hr := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) he
  have hh : (γ 0 1 : ℝ)=(δ 0 1 : ℝ)*(p:ℝ) := by
    simpa [lpsHeckeUpperGL,lpsHeckeUpperMatrix,Matrix.SpecialLinearGroup.mapGL,
      Matrix.map_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using hr
  exact_mod_cast hh.trans (mul_comm _ _)
end QEC.Coding.TannerLiftedProduct
