-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:38:17.347544+00:00
-- url     : https://prove2.me/submissions/adf358a2-e600-413d-a9b7-8e01f0aba436

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_finite_nonanalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphic_clear_by_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_interior_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∃ P : Polynomial ℂ, P.Monic ∧
      ∀ y : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      AnalyticAt ℂ (fun z => P.eval (lpsOriginalFilledJ N
        ((lpsOriginalFilledInteriorChart N hN y).symm z)) *
        F ((lpsOriginalFilledInteriorChart N hN y).symm z))
        (lpsOriginalFilledInteriorChart N hN y (Sum.inl y)) := by
  classical
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let Q := MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
  have hbad := lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN F hF
  have hbi : {y : Q | ¬ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (Sum.inl y)}.Finite :=
    Set.Finite.preimage Sum.inl_injective.injOn hbad
  let B : Finset Q := hbi.toFinset
  have hc (y : Q) : ∃ n : ℕ,
      AnalyticAt ℂ (fun z => (lpsOriginalFilledJ N
        ((lpsOriginalFilledInteriorChart N hN y).symm z) -
        lpsOriginalFilledJ N (Sum.inl y))^n *
        F ((lpsOriginalFilledInteriorChart N hN y).symm z))
        (lpsOriginalFilledInteriorChart N hN y (Sum.inl y)) := by
    let e := lpsOriginalFilledInteriorChart N hN y
    have hy : Sum.inl y ∈ e.source := lpsOriginalFilledInteriorChart_mem N hN y
    have hm := hF (Sum.inl y) (e (Sum.inl y)) (e.map_source hy)
    have hj := lpsOriginalFilledJ_interior_analytic N hN y
      (e (Sum.inl y)) (e.map_source hy)
    have h := lpsOriginalMeromorphic_clear_by_analytic_zero
      (F ∘ e.symm) (lpsOriginalFilledJ N ∘ e.symm) (e (Sum.inl y)) hm hj
    simpa only [Function.comp_apply,e.left_inv hy] using h
  let n : Q → ℕ := fun y => (hc y).choose
  let A : Q → Polynomial ℂ := fun y =>
    (Polynomial.X-Polynomial.C (lpsOriginalFilledJ N (Sum.inl y)))^(n y)
  let P := ∏ y ∈ B, A y
  have hA (y : Q) : (A y).Monic :=
    (Polynomial.monic_X_sub_C _).pow _
  refine ⟨P,Polynomial.monic_prod_of_monic _ _ (fun y hy => hA y),?_⟩
  intro y
  let e := lpsOriginalFilledInteriorChart N hN y
  let j : ℂ → ℂ := lpsOriginalFilledJ N ∘ e.symm
  let f : ℂ → ℂ := F ∘ e.symm
  let a := e (Sum.inl y)
  have hy : Sum.inl y ∈ e.source := lpsOriginalFilledInteriorChart_mem N hN y
  have hj : AnalyticAt ℂ j a :=
    lpsOriginalFilledJ_interior_analytic N hN y a (e.map_source hy)
  have heval (R : Polynomial ℂ) : AnalyticAt ℂ (fun z => R.eval (j z)) a := by
    simpa only [Polynomial.coe_aeval_eq_eval] using hj.aeval_polynomial R
  by_cases hmem : y ∈ B
  · have hclear : AnalyticAt ℂ (fun z => (A y).eval (j z) * f z) a := by
      simpa only [A,n,j,f,a,Polynomial.eval_pow,Polynomial.eval_sub,
        Polynomial.eval_X,Polynomial.eval_C,Function.comp_apply] using (hc y).choose_spec
    have hrest := heval (∏ b ∈ B.erase y, A b)
    have hprod : P = (∏ b ∈ B.erase y, A b) * A y :=
      (Finset.prod_erase_mul B A hmem).symm
    change AnalyticAt ℂ (fun z => P.eval (j z) * f z) a
    rw [hprod]
    convert! hrest.mul hclear using 1
    first
    | rfl
    | (funext z; simp only [Pi.mul_apply,Polynomial.eval_mul]; ring)
  · have hreg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (Sum.inl y) := by
      by_contra hn
      apply hmem
      exact (Set.Finite.mem_toFinset hbi).mpr hn
    have hf : AnalyticAt ℂ f a := by
      have hd := (contMDiffAt_iff_source.mp hreg)
      rw [contMDiffWithinAt_iff_contDiffWithinAt] at hd
      have hchart : chartAt ℂ (Sum.inl y : LPSOriginalFilledCurve N) = e := rfl
      have hdu : ContDiffAt ℂ ω f a := by
        simpa only [extChartAt_coe_symm,extChartAt_coe,
          modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
          Set.range_id,Function.comp_def,id_eq,contDiffWithinAt_univ,hchart,f,a]
          using hd
      exact hdu.analyticAt
    exact (heval P).mul hf
end QEC.Coding.TannerLiftedProduct
