-- Prove2me | solution 1 for WhitinPrice.LotSize.stationary_price_cubic
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:33:38.06736+00:00
-- url     : https://prove2.me/submissions/0cdd5c5c-4ab1-4bd1-9b95-d48d58d49960

import Definitions.Def_WhitinPrice_LotSize_Model

set_option autoImplicit false
open WhitinPrice.LotSize

theorem solution (S I C k f a b p : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C)
    (hD : 0 < demand a b p)
    (hstat : HasDerivAt (reducedProfit S I C k f a b) 0 p) :
    8 * a ^ 3 * p ^ 3 + (16 * a ^ 2 * b - 8 * k * a ^ 3) * p ^ 2 +
      (10 * a * b ^ 2 - 12 * k * a ^ 2 * b + 2 * k ^ 2 * a ^ 3) * p +
      2 * b ^ 3 - 4 * k * a * b ^ 2 + 2 * k ^ 2 * a ^ 2 * b - S * I * C * a ^ 2 = 0 := by
  have hpos : 0 < 2 * S * I * C * (a * p + b) := by
    change 0 < a * p + b at hD
    positivity
  let t := Real.sqrt (2 * S * I * C * (a * p + b))
  have ht : 0 < t := Real.sqrt_pos.2 hpos
  have htsq : t ^ 2 = 2 * S * I * C * (a * p + b) :=
    Real.sq_sqrt (le_of_lt hpos)
  have hdlin : HasDerivAt (fun x : ℝ => 2 * S * I * C * (a * x + b))
      (2 * S * I * C * a) p := by
    convert (((hasDerivAt_id p).const_mul a).add_const b).const_mul (2 * S * I * C) using 1 <;> first | rfl | (simp only [t, id_eq, pow_one]; ring) | ring
  have hdsqrt := hdlin.sqrt (ne_of_gt hpos)
  have hderiv : HasDerivAt (reducedProfit S I C k f a b)
      (2 * a * p + b - (2 * S * I * C * a) / (2 * t) - k * a) p := by
    convert (((((hasDerivAt_id p).pow 2).const_mul a).add
      ((hasDerivAt_id p).const_mul b)).sub hdsqrt).sub
      ((((hasDerivAt_id p).const_mul a).add_const b).const_mul k) |>.sub_const f using 1 <;> first | rfl | (simp only [t, id_eq, pow_one]; ring) | ring
  have hzero := hderiv.unique hstat
  have hrel : (2 * a * p + b - k * a) * t = S * I * C * a := by
    field_simp [ne_of_gt ht] at hzero
    nlinarith
  have hfactor : (S * I * C) *
      (2 * (a * p + b) * (2 * a * p + b - k * a) ^ 2 - S * I * C * a ^ 2) = 0 := by
    calc
      _ = (2 * a * p + b - k * a) ^ 2 * (2 * S * I * C * (a * p + b)) -
          (S * I * C * a) ^ 2 := by ring
      _ = ((2 * a * p + b - k * a) * t) ^ 2 - (S * I * C * a) ^ 2 := by rw [← htsq]; ring
      _ = 0 := by rw [hrel]; ring
  have hpoly : 2 * (a * p + b) * (2 * a * p + b - k * a) ^ 2 - S * I * C * a ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (by positivity)
  nlinarith only [hpoly]




