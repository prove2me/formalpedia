-- Prove2me | solution 1 for RatFunc.denom_coefficientRingEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:08.281457+00:00
-- url     : https://prove2.me/submissions/24b2bbef-5d06-4167-8dd9-d5afba691857

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
import Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
attribute [local simp] RatFunc.coefficientRingEquiv_apply_div

set_option autoImplicit false
open RatFunc
namespace RatFunc
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (x : RatFunc K) :
    (coefficientRingEquiv e x).denom =
      x.denom.map e.toRingHom := by
  let y := coefficientRingEquiv e x
  let P := x.num.map e.toRingHom
  let Q := x.denom.map e.toRingHom
  have hQ : Q ≠ 0 := Polynomial.map_ne_zero x.denom_ne_zero
  have hy : y = algebraMap (Polynomial L) (RatFunc L) P /
      algebraMap (Polynomial L) (RatFunc L) Q := by
    change coefficientRingEquiv e x = _
    rw [← x.num_div_denom]
    exact coefficientRingEquiv_apply_div e x.num x.denom
  have hcross : y.num * Q = P * y.denom :=
    (num_mul_eq_mul_denom_iff hQ).mpr hy
  have hPQ : IsCoprime P Q := by
    exact IsCoprime.map x.isCoprime_num_denom
      (Polynomial.mapRingHom e.toRingHom)
  have hyDenom_dvd_Q : y.denom ∣ Q := by
    apply y.isCoprime_num_denom.symm.dvd_of_dvd_mul_left
    exact ⟨P, by simpa [mul_comm] using hcross⟩
  have hQ_dvd_yDenom : Q ∣ y.denom := by
    apply hPQ.symm.dvd_of_dvd_mul_left
    exact ⟨y.num, by simpa [mul_comm] using hcross.symm⟩
  exact Polynomial.eq_of_monic_of_associated y.monic_denom
    (x.monic_denom.map e.toRingHom)
    (associated_of_dvd_dvd hyDenom_dvd_Q hQ_dvd_yDenom)
end RatFunc
