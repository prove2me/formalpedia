-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCosetCoefficient_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:09.670494+00:00
-- url     : https://prove2.me/submissions/f95a5f90-b342-4f87-acf8-5fb550359aa3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineKSeries_coeff_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateSeries_integral_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_eq_of_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateCusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateCusp_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateCusp_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalCosetCoefficient_clearedCusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_qpow
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hd : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hp : letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
      ∀ τ : ℍ, Φ.map ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ)))=
        ∏ x : (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
          (Polynomial.X-Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹•τ))))
    (k n : ℕ) : IsIntegral ℤ (((Φ.coeff k).coeff n:ℚ):ℂ) := by
  classical
  let d := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let p := (Φ.coeff k).map (algebraMap ℚ ℂ)
  let D := p.natDegree+N^2*d
  let E := N*D-N^2*(d-k)
  have hD : p.natDegree≤D := Nat.le_add_right _ _
  have hE : N^2*(d-k)≤N*D := by
    calc N^2*(d-k)≤N^2*d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
         _≤D := Nat.le_add_left _ _
         _≤N*D := by nlinarith
  obtain ⟨G,hG,hNomeG⟩ :=
    lpsOriginalRationalCosetCoefficient_clearedCusp N hN Φ hΦ hd hp k
  let F := lpsOriginalClearedUnivariateCusp N D p
  let H : ℂ→ℂ := fun q=>q^E*G.val q
  have hF : AnalyticAt ℂ F 0 :=
    lpsOriginalClearedUnivariateCusp_analytic N D hN.ne' p
  have hH : AnalyticAt ℂ H 0 := (lpsOriginalPower_analytic E).mul G.property
  have hNome : ∀ σ : ℍ, F (Function.Periodic.qParam 1 (σ:ℂ))=
      H (Function.Periodic.qParam 1 (σ:ℂ)) := by
    intro σ
    dsimp only [F]
    rw [lpsOriginalClearedUnivariateCusp_pullback N D hN p hD σ]
    dsimp only [H]
    rw [hNomeG σ]
    rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hE]
  have hDisk : ∀ q : ℂ, ‖q‖<1 → q≠0 → F q=H q := by
    intro q hq hq0
    let σ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqσ : Function.Periodic.qParam 1 (σ:ℂ)=q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    simpa only [hqσ] using hNome σ
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖<1 :=
    (isOpen_lt (continuous_norm : Continuous (fun q : ℂ=>‖q‖)) continuous_const).mem_nhds
      (by norm_num : ‖(0:ℂ)‖<1)
  have hePunctured : F=ᶠ[𝓝[≠] (0:ℂ)]H := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hq0
    exact hDisk q hq hq0
  have h0 : F 0=H 0 := tendsto_nhds_unique_of_eventuallyEq
    (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hePunctured
  have he : F=ᶠ[𝓝 0]H := by
    filter_upwards [hsmall] with q hq
    by_cases hq0 : q=0
    · subst q;exact h0
    · exact hDisk q hq hq0
  have hTaylor := lpsOriginalTaylorSeries_eq_of_germ hF hH he
  have hHT : lpsOriginalTaylorSeries H=PowerSeries.X^E*lpsOriginalCuspTaylorRingHom G := by
    change lpsOriginalTaylorSeries ((fun q : ℂ=>q^E)*G.val)=_
    rw [lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic E) G.property,
      lpsOriginalTaylorSeries_qpow]
    rfl
  have hc : ∀ t, IsIntegral ℤ ((lpsOriginalClearedUnivariateSeries N D
      (lpsOriginalTaylorSeries (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))) p).coeff t) := by
    intro t
    rw [←lpsOriginalClearedUnivariateCusp_taylor N D hN.ne' p,hTaylor,hHT,
      PowerSeries.coeff_X_pow_mul']
    split_ifs
    · exact hG _
    · exact isIntegral_zero
  have hK0 : (lpsOriginalTaylorSeries (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))).constantCoeff=1 := by
    rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,lpsOriginalTaylorSeries_coeff]
    simp [hN.ne',lpsOriginalJQCoefficient_zero]
  have hK : ∀ t, IsIntegral ℤ ((lpsOriginalTaylorSeries
      (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))).coeff t) := by
    intro t
    have hphase : Function.Periodic.qParam 1 ((0:ℚ):ℂ)=1 := by
      simp [Function.Periodic.qParam]
    simpa only [hphase,one_mul] using
      lpsOriginalAffineKSeries_coeff_integral 0 N hN.ne' t
  have hall := lpsOriginalClearedUnivariateSeries_integral_coeff N D hN
    _ p hD hK0 hK hc
  simpa only [p,Polynomial.coeff_map,eq_ratCast] using hall n
end QEC.Coding.TannerLiftedProduct
