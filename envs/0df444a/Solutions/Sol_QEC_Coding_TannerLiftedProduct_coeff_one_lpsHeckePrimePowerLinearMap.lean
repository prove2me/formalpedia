-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_one_lpsHeckePrimePowerLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:45:31.833201+00:00
-- url     : https://prove2.me/submissions/7cc4efbd-b55c-4e4e-9834-0324b5354084

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsCuspHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsCuspHecke_prime_power
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
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsHeckePrimePowerLinearMap N p hNp r f))=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) := by
  have hperiod : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  induction r using Nat.twoStepInduction generalizing f with
  | zero => rfl
  | one =>
    change PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f))=_
    rw [coeff_qExpansion_lpsCuspHecke]
    have hd : ¬p∣1 := (Fact.out : p.Prime).not_dvd_one
    simp [lpsModularDilationCoefficient,hd]
  | more r ih0 ih1 =>
    change PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
      (lpsHeckePrimePowerLinearMap N p hNp (r+1) (lpsCuspHecke N p hNp f)-
        (p:ℂ) • lpsHeckePrimePowerLinearMap N p hNp r f))=_
    have hs := ModularForm.qExpansion_sub (by norm_num : (0:ℝ)<1) hperiod
        (lpsHeckePrimePowerLinearMap N p hNp (r+1) (lpsCuspHecke N p hNp f))
        ((p:ℂ) • lpsHeckePrimePowerLinearMap N p hNp r f)
    simp only [FunLike.coe_smul] at hs
    rw [hs,ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1) hperiod (p:ℂ)
        (lpsHeckePrimePowerLinearMap N p hNp r f),
      map_sub,PowerSeries.coeff_smul,ih1,ih0]
    have h := coeff_qExpansion_lpsCuspHecke_prime_power N p hNp f (r+1)
    simpa only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,Nat.add_sub_cancel,
      smul_eq_mul] using h.symm
end QEC.Coding.TannerLiftedProduct
