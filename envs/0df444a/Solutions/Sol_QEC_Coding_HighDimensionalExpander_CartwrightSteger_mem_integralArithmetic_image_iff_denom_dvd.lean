-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_integralArithmetic_image_iff_denom_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:08.945658+00:00
-- url     : https://prove2.me/submissions/a21ecd42-8675-4a0e-a63b-d21e481fd87f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (x : FunctionField P) :
    (∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a = x) ↔
      ∃ n : ℕ, x.denom ∣
        (1 + Polynomial.X : PolynomialRing P) ^ n := by
  constructor
  · rintro ⟨a, rfl⟩
    have hone : (1 + Polynomial.X : PolynomialRing P) ≠ 0 := by
      intro h
      have := congrArg (Polynomial.eval (0 : BaseField P)) h
      simp at this
    obtain ⟨⟨p, s⟩, ha⟩ :=
      IsLocalization.surj
        (Submonoid.powers (1 + Polynomial.X : PolynomialRing P)) a
    obtain ⟨n, hn⟩ := s.property
    refine ⟨n, (RatFunc.denom_dvd
      (pow_ne_zero n hone)).mpr ?_⟩
    refine ⟨p, ?_⟩
    have hmap := congrArg (integralArithmeticToFunctionField P) ha
    simp only [map_mul, integralArithmeticToFunctionField_algebraMap] at hmap
    rw [← hn] at hmap
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero
      (pow_ne_zero n hone))).2
    simpa only using hmap
  · rintro ⟨n, hn⟩
    have hq : (1 + Polynomial.X : PolynomialRing P) ^ n ≠ 0 :=
      pow_ne_zero n (by
        intro h
        have := congrArg (Polynomial.eval (0 : BaseField P)) h
        simp at this)
    obtain ⟨p, hp⟩ := (RatFunc.denom_dvd hq).mp hn
    let s : Submonoid.powers
        (1 + Polynomial.X : PolynomialRing P) :=
      ⟨(1 + Polynomial.X) ^ n, ⟨n, rfl⟩⟩
    refine ⟨IsLocalization.mk' (IntegralArithmeticRing P) p s, ?_⟩
    let g : PolynomialRing P →+* FunctionField P :=
      algebraMap (PolynomialRing P) (FunctionField P)
    have hg : ∀ y : Submonoid.powers
        (1 + Polynomial.X : PolynomialRing P), IsUnit (g y) := by
      intro y
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      obtain ⟨k, hk⟩ := y.property
      rw [← hk]
      exact pow_ne_zero k (by
        intro h
        have := congrArg (Polynomial.eval (0 : BaseField P)) h
        simp at this)
    change IsLocalization.lift hg
        (IsLocalization.mk' (IntegralArithmeticRing P) p s) = x
    apply (IsLocalization.lift_mk'_spec hg p x s).2
    have hpMul := (eq_div_iff
      (RatFunc.algebraMap_ne_zero hq)).mp hp
    dsimp [g, s]
    simpa [mul_comm] using hpMul.symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
