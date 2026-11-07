-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.not_X_dvd_denom_of_building_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:28.601852+00:00
-- url     : https://prove2.me/submissions/df885fb5-0ecc-4db6-be2e-d220240e3f32

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (x : FunctionField P)
    (hlocal : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P x) :
    ¬ Polynomial.X ∣ x.denom := by
  have hxle : yAdicPlace P x ≤ 1 := by
    rw [RatFunc.valuation_eq_LaurentSeries_valuation]
    obtain ⟨f, hf⟩ := hlocal
    change (PowerSeries.idealX (BaseField P)).valuation
        (BuildingLocalField P) (functionFieldToBuildingLocalField P x) ≤ 1
    rw [← hf]
    change (PowerSeries.idealX (BaseField P)).valuation
        (BuildingLocalField P)
        (algebraMap (BuildingIntegerRing P) (BuildingLocalField P) f) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (PowerSeries.idealX (BaseField P)).intValuation_le_one f
  intro hden
  have hnum : ¬ Polynomial.X ∣ x.num := by
    intro hn
    exact Polynomial.not_isUnit_X
      (x.isCoprime_num_denom.isUnit_of_dvd' hn hden)
  let v := Polynomial.idealX (BaseField P)
  have hnumLe : v.intValuation x.num ≤ 1 :=
    v.intValuation_le_one x.num
  have hnumNotLt : ¬ v.intValuation x.num < 1 := by
    rw [v.intValuation_lt_one_iff_mem, Polynomial.idealX_span,
      Ideal.mem_span_singleton]
    exact hnum
  have hnumEq : v.intValuation x.num = 1 :=
    le_antisymm hnumLe (not_lt.mp hnumNotLt)
  have hdenLt : v.intValuation x.denom < 1 := by
    rw [v.intValuation_lt_one_iff_mem, Polynomial.idealX_span,
      Ideal.mem_span_singleton]
    exact hden
  have hdenPos : 0 < v.intValuation x.denom :=
    v.intValuation_zero_lt
      ⟨x.denom, mem_nonZeroDivisors_iff_ne_zero.mpr
        (RatFunc.denom_ne_zero x)⟩
  have hxgt : 1 < yAdicPlace P x := by
    rw [← x.num_div_denom]
    rw [map_div₀,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      hnumEq, one_div]
    exact (one_lt_inv₀ hdenPos).mpr hdenLt
  exact (not_lt_of_ge hxle) hxgt
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
