-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_separable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:05:32.497936+00:00
-- url     : https://prove2.me/submissions/2e175351-0d60-404a-956e-35216930dd9c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLevelJPolynomialEval_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_residueFractionSeparable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhaseResidue_charP
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldCuspSeries_domain
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalModularPolynomialModFraction N hN p).Separable := by
  let hp : p.Prime := Fact.out
  let K := LPSOriginalLevelPhaseResidue N hN p hp
  let : CharP K p := lpsOriginalLevelPhaseResidue_charP N hN p hp
  let L := FractionRing (lpsOriginalCuspSeriesRing K)
  let κ : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  let e : Polynomial (ZMod p) →+* lpsOriginalCuspSeriesRing K :=
    (lpsOriginalFieldLevelJPolynomialEval K N hN).comp (Polynomial.mapRingHom κ)
  have he : Function.Injective e :=
    (lpsOriginalFieldLevelJPolynomialEval_injective K N hN).comp
      (Polynomial.map_injective κ (ZMod.castHom_injective K))
  let g : Polynomial (ZMod p) →+* L :=
    (algebraMap (lpsOriginalCuspSeriesRing K) L).comp e
  have hg : Function.Injective g :=
    (IsFractionRing.injective (lpsOriginalCuspSeriesRing K) L).comp he
  let f : FractionRing (Polynomial (ZMod p)) →+* L := IsFractionRing.lift hg
  have hc : f.comp
      ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      (algebraMap (lpsOriginalCuspSeriesRing K) L).comp
        (lpsOriginalResidueLevelCoefficientEval N hN p hp) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp [f,g,e,κ,lpsOriginalFieldLevelJPolynomialEval,
        lpsOriginalResidueLevelCoefficientEval]
    · simp [f,g,e,κ,lpsOriginalFieldLevelJPolynomialEval,
        lpsOriginalResidueLevelCoefficientEval]
      rfl
  apply (Polynomial.separable_map f).mp
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.map_map,hc]
  exact lpsOriginalIntegerPolynomial_residueFractionSeparable N hN p hp hpN
end QEC.Coding.TannerLiftedProduct
