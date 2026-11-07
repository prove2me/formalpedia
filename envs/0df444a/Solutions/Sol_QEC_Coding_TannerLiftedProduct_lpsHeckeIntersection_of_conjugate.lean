-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_of_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:14:28.738785+00:00
-- url     : https://prove2.me/submissions/51970c47-170f-4c87-9438-3233d721d64e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
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
    (γ δ : SL(2,ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 N)
    (he : lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none) :
    γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by
  have hr := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0) he
  have hz : γ 1 0 = (δ 1 0)*(p:ℤ) := by
    have hh : (γ 1 0 : ℝ)=(δ 1 0 : ℝ)*(p:ℝ) := by
      simpa [lpsHeckeUpperGL,lpsHeckeUpperMatrix,Matrix.SpecialLinearGroup.mapGL,
        Matrix.map_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using hr
    exact_mod_cast hh
  rw [CongruenceSubgroup.Gamma0_mem] at hδ ⊢
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) N).mp hδ
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (N*p)).mpr
  obtain ⟨t,ht⟩ := hd
  refine ⟨t,?_⟩
  rw [hz,ht]
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct
