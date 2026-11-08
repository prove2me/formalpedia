-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaEisensteinCorrection_even_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:31:29.345737+00:00
-- url     : https://prove2.me/submissions/f5c51037-2d3c-4887-aeb5-29651ff32c75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaEisensteinCorrection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinCorrectionCoefficient_of_unit_characters
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_square


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p q : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hp : Odd p) (hpq : ¬q∣p) (n : ℕ) :
    PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1 (lpsThetaEisensteinCorrection q hq2))=
      4*(ArithmeticFunction.sigma 1 (p^(2*n)):ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by
  have h2 : ¬2∣p^(2*n) := (hp.pow).not_two_dvd_nat
  have hq : ¬q∣p^(2*n) := fun hd => hpq ((Fact.out : q.Prime).dvd_of_dvd_pow hd)
  have hc4 : lpsChi4E2Character ((p^(2*n):ℕ):ZMod 4)=1 := by
    have hc : (p^n).Coprime 4 := by
      have h := (hp.pow : Odd (p^n)).coprime_two_right.pow_right 2
      norm_num only [Nat.reducePow] at h
      exact h
    have hu : IsUnit ((p^n:ℕ):ZMod 4) := (ZMod.isUnit_iff_coprime (p^n) 4).mpr hc
    rw [show p^(2*n)=(p^n)^2 by rw [mul_comm,pow_mul],Nat.cast_pow]
    exact lpsChi4E2Character_square _ hu
  have hcq : lpsQuadraticE2Character q ((p^(2*n):ℕ):ZMod q)=1 := by
    have hn : ((p^n:ℕ):ZMod q)≠0 := by
      intro hz
      have hd : q∣p^n := (ZMod.natCast_eq_zero_iff (p^n) q).mp hz
      exact hpq ((Fact.out : q.Prime).dvd_of_dvd_pow hd)
    rw [show p^(2*n)=(p^n)^2 by rw [mul_comm,pow_mul],Nat.cast_pow]
    exact lpsQuadraticE2Character_square q _ hn
  rw [coeff_qExpansion_lpsThetaEisensteinCorrection]
  exact lpsThetaEisensteinCorrectionCoefficient_of_unit_characters q _ h2 hq hc4 hcq
end QEC.Coding.TannerLiftedProduct
