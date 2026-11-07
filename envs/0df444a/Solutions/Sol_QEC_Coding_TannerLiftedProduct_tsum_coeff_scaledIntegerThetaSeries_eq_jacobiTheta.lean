-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_coeff_scaledIntegerThetaSeries_eq_jacobiTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:23.458989+00:00
-- url     : https://prove2.me/submissions/d0f62aba-f5d1-4e85-a150-579c6e105e9b

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
    (m : ℕ) (hm : 0 < m) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      jacobiTheta ((m ^ 2 : ℕ) * τ) := by
  let q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hScaledIm : 0 < (((m ^ 2 : ℕ) : ℂ) * τ).im := by
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast pow_pos hm 2) hτ
  have hSummable : Summable (fun z : ℤ =>
      Complex.exp (Real.pi * Complex.I *
        (((m : ℂ) ^ 2) * (z : ℂ) ^ 2) * τ)) := by
    convert summable_exp_integer_square (((m ^ 2 : ℕ) : ℂ) * τ) hScaledIm using 1
    ext z
    congr 1
    push_cast
    ring
  have hFiber := hSummable.hasSum.tsum_fiberwise
    (fun z : ℤ => m ^ 2 * z.natAbs ^ 2)
  change HasSum (fun n : ℕ =>
    ∑' z : {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n},
      Complex.exp (Real.pi * Complex.I *
        ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ))
    (∑' z : ℤ,
      Complex.exp (Real.pi * Complex.I *
        ((m : ℂ) ^ 2 * (z : ℂ) ^ 2) * τ)) at hFiber
  have hTerm (n : ℕ) :
      (∑' z : {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n},
        Complex.exp (Real.pi * Complex.I *
          ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ)) =
      ((PowerSeries.coeff n (scaledIntegerThetaSeries m) : ℕ) : ℂ) * q ^ n := by
    letI : Fintype {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n} :=
      scaledIntegerSquareFibreFintype m n hm
    have hExp (z : {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n}) :
        Complex.exp (Real.pi * Complex.I *
          ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ) = q ^ n := by
      have hsInt : ((z.1.natAbs ^ 2 : ℕ) : ℤ) = z.1 ^ 2 := by
        simp [sq_abs]
      have hsComplex : ((z.1.natAbs ^ 2 : ℕ) : ℂ) = (z.1 : ℂ) ^ 2 := by
        calc
          ((z.1.natAbs ^ 2 : ℕ) : ℂ) =
              (((z.1.natAbs ^ 2 : ℕ) : ℤ) : ℂ) := by norm_cast
          _ = ((z.1 ^ 2 : ℤ) : ℂ) := congrArg (fun x : ℤ => (x : ℂ)) hsInt
          _ = (z.1 : ℂ) ^ 2 := by norm_cast
      have hs : ((m ^ 2 * z.1.natAbs ^ 2 : ℕ) : ℂ) =
          (m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2 := by
        calc
          ((m ^ 2 * z.1.natAbs ^ 2 : ℕ) : ℂ) =
              (m : ℂ) ^ 2 * ((z.1.natAbs ^ 2 : ℕ) : ℂ) := by norm_cast
          _ = (m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2 := by rw [hsComplex]
      calc
        Complex.exp (Real.pi * Complex.I *
            ((m : ℂ) ^ 2 * (z.1 : ℂ) ^ 2) * τ) =
            Complex.exp (((m ^ 2 * z.1.natAbs ^ 2 : ℕ) : ℂ) *
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
    have hCard : Fintype.card {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n} =
        (scaledIntegerSquareRoots m n).card := by
      calc
        Fintype.card {z : ℤ | m ^ 2 * z.natAbs ^ 2 = n} =
            Fintype.card {z : ℤ // z ∈ scaledIntegerSquareRoots m n} :=
          Fintype.card_congr
            (Equiv.subtypeEquivRight
              (scaledNatAbs_sq_eq_iff_mem_scaledIntegerSquareRoots m n hm))
        _ = (scaledIntegerSquareRoots m n).card := Fintype.card_coe _
    simp [hCard, coeff_scaledIntegerThetaSeries]
  have hEq := hFiber.tsum_eq
  simp_rw [hTerm] at hEq
  have hAnalytic :
      (∑' z : ℤ,
        Complex.exp (Real.pi * Complex.I *
          ((m : ℂ) ^ 2 * (z : ℂ) ^ 2) * τ)) =
      jacobiTheta ((m ^ 2 : ℕ) * τ) := by
    unfold jacobiTheta
    apply tsum_congr
    intro z
    congr 1
    push_cast
    ring
  rw [hAnalytic] at hEq
  simpa [q] using hEq
end QEC.Coding.TannerLiftedProduct
