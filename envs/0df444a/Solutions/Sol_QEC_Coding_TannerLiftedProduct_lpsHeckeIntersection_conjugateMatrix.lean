-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_conjugateMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:14:13.976206+00:00
-- url     : https://prove2.me/submissions/042fd838-46d2-4450-b146-14184ad053fa

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
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N*p)) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p none * (γ:Matrix (Fin 2) (Fin 2) ℤ) =
        (δ:Matrix (Fin 2) (Fin 2) ℤ) * lpsHeckeUpperMatrix p none := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  obtain ⟨t,ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (N*p)).mp hγ
  have hc : γ 1 0 = (p:ℤ)*((N:ℤ)*t) := by
    rw [ht]
    push_cast
    ring
  let δ := lpsE2DilationConjugate p γ ((N:ℤ)*t) hc
  have hδ : δ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    change (((N:ℤ)*t:ℤ):ZMod N)=0
    simp
  refine ⟨δ,hδ,?_⟩
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,δ,lpsE2DilationConjugate,hc,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,mul_comm]
end QEC.Coding.TannerLiftedProduct
