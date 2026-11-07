-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrectionCoefficient_of_unit_characters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:35:32.377135+00:00
-- url     : https://prove2.me/submissions/2e4c6c26-7481-44c1-8b02-74eabf3c3e57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2DifferenceCoefficient_of_not_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (n : ℕ) (h2 : ¬2∣n) (hq : ¬q∣n)
    (hc4 : lpsChi4E2Character (n:ZMod 4)=1)
    (hcq : lpsQuadraticE2Character q (n:ZMod q)=1) :
    lpsThetaEisensteinCorrectionCoefficient q n=
      4*(ArithmeticFunction.sigma 1 n:ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by
  have hn : n≠0 := by intro hn;subst n;exact h2 (dvd_zero _)
  have hpd (a b : ℕ) (hab : 0<a ∨ 0<b) : ¬2^a*q^b∣n := by
    intro hd
    rcases hab with ha | hb
    · exact h2 ((dvd_pow_self 2 ha.ne').trans ((dvd_mul_right (2^a) (q^b)).trans hd))
    · exact hq ((dvd_pow_self q hb.ne').trans ((dvd_mul_left (q^b) (2^a)).trans hd))
  have hq2 : ¬q^2∣n := fun hd => hq ((dvd_pow_self q (by decide : (2:ℕ)≠0)).trans hd)
  have h4 : ¬4∣n := fun hd => h2 ((by decide : (2:ℕ)∣4).trans hd)
  have h8 : ¬8∣n := fun hd => h2 ((by decide : (2:ℕ)∣8).trans hd)
  have h16 : ¬16∣n := fun hd => h2 ((by decide : (2:ℕ)∣16).trans hd)
  have hqC : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hq2C : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hx : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hx
  have hH (a b : ℕ) : lpsE2DifferenceCoefficient (2^a*q^b) n=
      if a=0 ∧ b=0 then 0 else -24*(ArithmeticFunction.sigma 1 n:ℂ) := by
    by_cases ha : a=0
    · subst a
      by_cases hb : b=0
      · subst b
        simp [lpsE2DifferenceCoefficient,lpsE2DilationCoefficient]
      · rw [lpsE2DifferenceCoefficient_of_not_dvd _ n hn (hpd _ _ (Or.inr (Nat.pos_of_ne_zero hb)))]
        simp [hb]
    · rw [lpsE2DifferenceCoefficient_of_not_dvd _ n hn (hpd _ _ (Or.inl (Nat.pos_of_ne_zero ha)))]
      simp [ha]
  simp only [lpsThetaEisensteinCorrectionCoefficient]
  simp_rw [hH]
  norm_num [Fin.sum_univ_succ,lpsThetaEisensteinTwoWeight,lpsThetaEisensteinPrimeWeight,
    lpsThetaEisensteinChi4Weight,lpsThetaEisensteinQuadraticWeight,hq,hq2,h2,h4,h8,h16,hcq,hc4]
  simp only [lpsThetaEisensteinNormalization]
  field_simp [hqC,hq2C]
  ring
end QEC.Coding.TannerLiftedProduct
