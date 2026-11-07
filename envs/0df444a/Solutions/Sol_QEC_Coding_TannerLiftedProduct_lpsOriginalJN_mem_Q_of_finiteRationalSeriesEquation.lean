-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:46:05.183511+00:00
-- url     : https://prove2.me/submissions/364f320a-f952-436e-96f1-6cd399ff3886

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphic_zero_of_clearedNomeGerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalMonomialHolomorphicSum_mem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_formal_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_qParam_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQSeries_dilated_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_qpow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_sub
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ
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
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {ι : Type*} [Fintype ι] (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a b : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B)
    (h :
      PowerSeries.X ^ N * (∑ i, PowerSeries.C (a i) *
        lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) =
      PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries *
        (∑ i, PowerSeries.C (b i) *
          lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)))
    (hb : (∑ i, PowerSeries.C (b i) *
      lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) ≠ 0) :
    lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionFieldQ M hM := by
  classical
  let Ga := lpsOriginalFiniteClearedRationalSum M B u v a
  let Gb := lpsOriginalFiniteClearedRationalSum M B u v b
  let Ha := lpsOriginalRationalMonomialHolomorphicSum M hM u v a
  let Hb := lpsOriginalRationalMonomialHolomorphicSum M hM u v b
  let KN : ℂ → ℂ := fun q => lpsOriginalJQCoefficient (q ^ N)
  have ha0 : AnalyticAt ℂ Ga 0 :=
    lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v a
  have hb0 : AnalyticAt ℂ Gb 0 :=
    lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v b
  have hKN : AnalyticAt ℂ KN 0 :=
    lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow (Nat.ne_of_gt hN))
  let D := KN * Gb - (fun q : ℂ => q ^ N) * Ga
  have hD : AnalyticAt ℂ D 0 := (hKN.mul hb0).sub ((lpsOriginalPower_analytic N).mul ha0)
  have hT : lpsOriginalTaylorSeries D = 0 := by
    rw [lpsOriginalTaylorSeries_sub (hKN.mul hb0) ((lpsOriginalPower_analytic N).mul ha0),
      lpsOriginalTaylorSeries_mul hKN hb0,
      lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic N) ha0,
      lpsOriginalTaylorSeries_qpow]
    change lpsOriginalTaylorSeries KN * lpsOriginalTaylorSeries
      (lpsOriginalFiniteClearedRationalSum M B u v b) -
        PowerSeries.X ^ N * lpsOriginalTaylorSeries
          (lpsOriginalFiniteClearedRationalSum M B u v a) = 0
    rw [lpsOriginalFiniteClearedRationalSum_taylor M (Nat.ne_of_gt hM),
      lpsOriginalFiniteClearedRationalSum_taylor M (Nat.ne_of_gt hM)]
    change lpsOriginalTaylorSeries (fun q => lpsOriginalJQCoefficient (q ^ N)) * _ - _ = 0
    rw [← lpsOriginalJQSeries_dilated_map N (Nat.ne_of_gt hN)]
    have hm := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) h
    simp only [map_mul, map_pow, PowerSeries.map_X] at hm
    exact sub_eq_zero.mpr hm.symm
  have hg := (lpsOriginalTaylorSeries_zero_iff_germ hD).mp hT
  have hz : lpsOriginalJNHolomorphic N hN * Hb - Ha = 0 := by
    apply lpsOriginalHolomorphic_zero_of_clearedNomeGerm
      (lpsOriginalJNHolomorphic N hN * Hb - Ha) D (B + N) hg
    intro τ
    change lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (τ : ℂ) ^ N) *
      lpsOriginalFiniteClearedRationalSum M B u v b
        (Function.Periodic.qParam 1 (τ : ℂ)) -
      Function.Periodic.qParam 1 (τ : ℂ) ^ N *
        lpsOriginalFiniteClearedRationalSum M B u v a
          (Function.Periodic.qParam 1 (τ : ℂ)) = _
    rw [lpsOriginalFiniteClearedRationalSum_pullback M hM B u v b hB τ,
      lpsOriginalFiniteClearedRationalSum_pullback M hM B u v a hB τ,
      ← lpsOriginalJDilated_qParam_pullback N hN τ]
    change _ = Function.Periodic.qParam 1 (τ : ℂ) ^ (B + N) *
      (lpsOriginalJDilated N hN τ * Hb.val τ - Ha.val τ)
    rw [pow_add]
    ring
  have hHb : Hb ≠ 0 := lpsOriginalFiniteClearedRationalSum_formal_ne_zero
    M hM B u v b hB hb
  let holoMap := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hHb' : holoMap Hb ≠ 0 := fun he =>
    hHb (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (he.trans (map_zero holoMap).symm))
  have hmul : lpsOriginalJNInFractionField N hN * holoMap Hb = holoMap Ha := by
    have he := congrArg holoMap (sub_eq_zero.mp hz)
    simpa only [map_mul, lpsOriginalJNInFractionField] using he
  rw [(eq_div_iff hHb').mpr hmul]
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalGeneratedFunctionFieldQ M hM).div_mem
    (lpsOriginalRationalMonomialHolomorphicSum_mem M hM u v a)
    (lpsOriginalRationalMonomialHolomorphicSum_mem M hM u v b)
end QEC.Coding.TannerLiftedProduct
