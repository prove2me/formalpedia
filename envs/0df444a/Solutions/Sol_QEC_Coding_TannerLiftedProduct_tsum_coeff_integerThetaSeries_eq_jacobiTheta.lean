-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_coeff_integerThetaSeries_eq_jacobiTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:22.281135+00:00
-- url     : https://prove2.me/submissions/4ce4bd57-3693-4071-93b3-888214848336

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_exp_integer_square
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) = jacobiTheta τ := by
  let q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hFiber := (summable_exp_integer_square τ hτ).hasSum.tsum_fiberwise
    (fun z : ℤ => z.natAbs ^ 2)
  change HasSum (fun n : ℕ =>
    ∑' z : {z : ℤ | z.natAbs ^ 2 = n},
      Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ))
    (∑' z : ℤ, Complex.exp (Real.pi * Complex.I * (z : ℂ) ^ 2 * τ)) at hFiber
  have hTerm (n : ℕ) :
      (∑' z : {z : ℤ | z.natAbs ^ 2 = n},
        Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ)) =
      ((PowerSeries.coeff n integerThetaSeries : ℕ) : ℂ) * q ^ n := by
    letI : Fintype {z : ℤ | z.natAbs ^ 2 = n} := integerSquareFibreFintype n
    have hExp (z : {z : ℤ | z.natAbs ^ 2 = n}) :
        Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ) = q ^ n := by
      have hs : ((z.1.natAbs ^ 2 : ℕ) : ℂ) = (z.1 : ℂ) ^ 2 := by
        have hsInt : ((z.1.natAbs ^ 2 : ℕ) : ℤ) = z.1 ^ 2 := by
          simp [sq_abs]
        calc
          ((z.1.natAbs ^ 2 : ℕ) : ℂ) =
              (((z.1.natAbs ^ 2 : ℕ) : ℤ) : ℂ) := by norm_cast
          _ = ((z.1 ^ 2 : ℤ) : ℂ) :=
            congrArg (fun x : ℤ => (x : ℂ)) hsInt
          _ = (z.1 : ℂ) ^ 2 := by norm_cast
      calc
        Complex.exp (Real.pi * Complex.I * (z.1 : ℂ) ^ 2 * τ) =
            Complex.exp (((z.1.natAbs ^ 2 : ℕ) : ℂ) *
              (Real.pi * Complex.I * τ)) := by
          congr 1
          rw [hs]
          ring
        _ = Complex.exp ((n : ℂ) * (Real.pi * Complex.I * τ)) := by
          rw [z.2]
        _ = q ^ n := by simpa [q] using
          (Complex.exp_nat_mul (Real.pi * Complex.I * τ) n)
    rw [tsum_fintype]
    simp_rw [hExp]
    have hCard : Fintype.card {z : ℤ | z.natAbs ^ 2 = n} =
        (integerSquareRoots n).card := by
      calc
        Fintype.card {z : ℤ | z.natAbs ^ 2 = n} =
            Fintype.card {z : ℤ // z ∈ integerSquareRoots n} :=
          Fintype.card_congr
            (Equiv.subtypeEquivRight
              (natAbs_sq_eq_iff_mem_integerSquareRoots n))
        _ = (integerSquareRoots n).card := Fintype.card_coe _
    simp [hCard, coeff_integerThetaSeries]
  have hEq := hFiber.tsum_eq
  simp_rw [hTerm] at hEq
  simpa [jacobiTheta, q] using hEq
end QEC.Coding.TannerLiftedProduct
