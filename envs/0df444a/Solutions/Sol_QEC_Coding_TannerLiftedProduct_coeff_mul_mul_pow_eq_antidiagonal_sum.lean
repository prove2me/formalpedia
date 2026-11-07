-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_mul_mul_pow_eq_antidiagonal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:39:59.963792+00:00
-- url     : https://prove2.me/submissions/98c3970e-c293-457e-a651-adf632c92976

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (S T : PowerSeries ℕ) (z : ℂ) (n : ℕ) :
    ((PowerSeries.coeff n (S * T) : ℕ) : ℂ) * z ^ n =
      ∑ kl ∈ Finset.antidiagonal n,
        (((PowerSeries.coeff kl.1 S : ℕ) : ℂ) * z ^ kl.1) *
          (((PowerSeries.coeff kl.2 T : ℕ) : ℂ) * z ^ kl.2) := by
  rw [PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hAdd : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  rw [← hAdd, pow_add]
  ring
end QEC.Coding.TannerLiftedProduct
