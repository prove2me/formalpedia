-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Translate_integerPeriod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:53.324475+00:00
-- url     : https://prove2.me/submissions/fd926ca6-7ca7-4614-9ebb-c97c45013286

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
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
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (ρ : SL(2,ℤ)) :
    (N:ℝ)∈(ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff,ConjAct.toConjAct_inv,
    Subgroup.mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul]
  have ht : ModularGroup.T^(N:ℤ)∈CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N:ℤ) (N:ℤ) (dvd_refl _)
  have hc := (CongruenceSubgroup.Gamma_normal N).conj_mem _ ht ρ
  have hg : ρ*(ModularGroup.T^(N:ℤ))*ρ⁻¹∈CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma_mem] at hc
    rw [CongruenceSubgroup.Gamma0_mem]
    exact hc.2.2.1
  have he : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T^(N:ℤ))=
      Matrix.GeneralLinearGroup.upperRightHom (N:ℝ) := by
    apply Units.ext
    change ((ModularGroup.T^(N:ℤ):SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.castRingHom ℝ)=_
    rw [ModularGroup.coe_T_zpow]
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  have hmap := Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hg
  simpa only [map_mul,map_inv,he] using hmap
end QEC.Coding.TannerLiftedProduct
