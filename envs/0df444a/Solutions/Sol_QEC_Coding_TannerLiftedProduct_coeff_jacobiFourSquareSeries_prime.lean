-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:37:19.410753+00:00
-- url     : https://prove2.me/submissions/b59fdc3a-d094-4a2c-985c-9f25c8863caf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    PowerSeries.coeff p jacobiFourSquareSeries = 8 * (p + 1) := by
  have h4p : ¬ 4 ∣ p := by
    intro h
    have hzero := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  simp only [jacobiFourSquareSeries, PowerSeries.coeff_mk,
    if_neg hp.ne_zero, hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm)]
  simp [h4p, Nat.add_comm]
end QEC.Coding.TannerLiftedProduct
