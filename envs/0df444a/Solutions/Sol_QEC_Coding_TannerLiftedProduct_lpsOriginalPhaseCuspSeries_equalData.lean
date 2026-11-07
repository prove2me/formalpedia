-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_equalData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:01:15.323344+00:00
-- url     : https://prove2.me/submissions/785568ea-6c44-433b-a929-071d6f601c47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_clear
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_neZero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_inversePower
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_ne_of_slope_lt
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeriesAlgebraMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type*) [CommRing R] [IsDomain R]
    (N : ℕ) (hN : 0 < N) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ζ η : R) (hζ : ζ^N = 1) (hη : η^N = 1)
    (he : lpsOriginalPhaseCuspSeries R N m hm ζ =
      lpsOriginalPhaseCuspSeries R N n hn η) : m = n ∧ ζ = η := by
  have hmn : m = n := by
    rcases lt_trichotomy m n with h | h | h
    · exact False.elim ((lpsOriginalPhaseCuspSeries_ne_of_slope_lt
        R N hN m n hm hn ζ η hη h) he)
    · exact h
    · exact False.elim ((lpsOriginalPhaseCuspSeries_ne_of_slope_lt
        R N hN n m hn hm η ζ hζ h) he.symm)
  refine ⟨hmn, ?_⟩
  subst n
  have hc := congrArg (fun j : lpsOriginalCuspSeriesRing R =>
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^m * j) he
  rw [lpsOriginalPhaseCuspSeries_clear R N m hm ζ m (le_refl m),
    lpsOriginalPhaseCuspSeries_clear R N m hm η m (le_refl m)] at hc
  simp only [Nat.sub_self,pow_zero,one_mul] at hc
  have hs := lpsOriginalCuspSeriesAlgebraMap_injective R hc
  have hi := congrArg PowerSeries.constantCoeff hs
  rw [lpsOriginalPhaseCuspNumerator_constant,
    lpsOriginalPhaseCuspNumerator_constant] at hi
  apply mul_right_cancel₀ (pow_ne_zero (N-1)
    (lpsOriginalLevelRoot_neZero R N hN η hη))
  calc
    ζ * η^(N-1) = ζ * ζ^(N-1) := by rw [hi]
    _ = 1 := lpsOriginalLevelRoot_inversePower R N hN ζ hζ
    _ = η * η^(N-1) := (lpsOriginalLevelRoot_inversePower R N hN η hη).symm
end QEC.Coding.TannerLiftedProduct
