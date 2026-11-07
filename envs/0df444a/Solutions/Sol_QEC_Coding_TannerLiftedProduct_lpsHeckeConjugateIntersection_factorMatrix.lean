-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_factorMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:15:00.568387+00:00
-- url     : https://prove2.me/submissions/9bd56b9d-7965-46a5-b838-b54f299033c1

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
    (γ : SL(2,ℤ)) (hγ : γ ∈ lpsHeckeConjugateIntersection N p) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p (some ⟨0,(Fact.out:p.Prime).pos⟩) *
          (γ:Matrix (Fin 2) (Fin 2) ℤ) =
        (δ:Matrix (Fin 2) (Fin 2) ℤ) *
          lpsHeckeUpperMatrix p (some ⟨0,(Fact.out:p.Prime).pos⟩) := by
  obtain ⟨hγN,t,ht⟩ := (lpsHeckeConjugateIntersection_mem N p γ).mp hγ
  have hd : Matrix.det !![γ 0 0,t;(p:ℤ)*γ 1 0,γ 1 1]=1 := by
    have hd := γ.det_coe
    rw [Matrix.det_fin_two] at hd ⊢
    change γ 0 0*γ 1 1-t*((p:ℤ)*γ 1 0)=1
    change γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 at hd
    rw [ht] at hd
    linear_combination hd
  let δ : SL(2,ℤ) := ⟨!![γ 0 0,t;(p:ℤ)*γ 1 0,γ 1 1],hd⟩
  have hδ : δ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    change (((p:ℤ)*γ 1 0:ℤ):ZMod N)=0
    simp [CongruenceSubgroup.Gamma0_mem.mp hγN]
  refine ⟨δ,hδ,?_⟩
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,δ,ht,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,mul_comm]
end QEC.Coding.TannerLiftedProduct
