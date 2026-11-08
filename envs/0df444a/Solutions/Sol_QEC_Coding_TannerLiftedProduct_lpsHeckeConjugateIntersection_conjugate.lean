-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:07:04.33707+00:00
-- url     : https://prove2.me/submissions/c64eebc7-3836-4c4b-86ca-ad34ea6edd67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_mem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_factorMatrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightFactorGL
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
    (δ : SL(2,ℤ)) (hδ : δ ∈ lpsHeckeConjugateIntersection N p) :
    ∃γ : SL(2,ℤ),γ ∈ CongruenceSubgroup.Gamma0 (N*p) ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by
  obtain ⟨γ,_hγ,he⟩ := lpsHeckeConjugateIntersection_factorMatrix N p δ hδ
  have hc := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) he
  have hz : γ 1 0=(p:ℤ)*δ 1 0 := by
    simpa [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] using hc.symm
  have hdN := (lpsHeckeConjugateIntersection_mem N p δ).mp hδ |>.1
  rw [CongruenceSubgroup.Gamma0_mem] at hdN
  obtain ⟨t,ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hdN
  have hγNp : γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (N*p)).mpr
    refine ⟨t,?_⟩
    rw [hz,ht]
    push_cast
    ring
  refine ⟨γ,hγNp,?_⟩
  have hmatrix : lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p none := by
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 0) he
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1) he
    have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 1) he
    simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h11
    have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
    have hd : γ 1 1=δ 1 1 := mul_left_cancel₀ hp (by simpa only [mul_comm] using h11.symm)
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,←h00,h01,hz,hd,mul_comm]
  exact lpsHeckeRightFactorGL ℝ p none none γ δ hmatrix
end QEC.Coding.TannerLiftedProduct
