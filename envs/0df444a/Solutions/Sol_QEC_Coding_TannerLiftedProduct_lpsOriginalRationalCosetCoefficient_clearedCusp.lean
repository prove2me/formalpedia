-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCosetCoefficient_clearedCusp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:54:01.9302+00:00
-- url     : https://prove2.me/submissions/4fc23001-09fd-41ce-9f83-ee46631e7a1e

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSLAtScaledCuspRational
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_integral_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralCosetProduct_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalScaleRootsCosetProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
    (k : ℕ) :
    ∃ G : lpsOriginalCuspAnalyticSubring,
      (∀ n, IsIntegral ℤ ((lpsOriginalCuspTaylorRingHom G).coeff n)) ∧
      ∀ σ : ℍ, G.val (Function.Periodic.qParam 1 (σ:ℂ))=
        Function.Periodic.qParam 1 (σ:ℂ)^(N^2*(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)-k)) *
          ((Φ.coeff k).map (algebraMap ℚ ℂ)).eval (lpsOriginalJDilated N hN σ) := by
  classical
  let I := 𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ
  let := Fintype.ofFinite I
  choose m hm r hle hr using
    (fun x : I => lpsOriginalSLAtScaledCuspRational N hN x.out⁻¹)
  let A : I→lpsOriginalCuspAnalyticSubring := fun x =>
    ⟨lpsOriginalClearedAffineCusp (N^2) (m x) (r x),
      lpsOriginalClearedAffineCusp_analytic (N^2) (m x) (hm x).ne' (r x)⟩
  let S : Polynomial lpsOriginalCuspAnalyticSubring :=
    ∏ x : I, (Polynomial.X-Polynomial.C (A x))
  let G := S.coeff k
  refine ⟨G,?_,?_⟩
  · intro n
    change IsIntegral ℤ ((lpsOriginalCuspTaylorRingHom (S.coeff k)).coeff n)
    rw [←Polynomial.coeff_map]
    simp only [S,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    apply lpsOriginalIntegralCosetProduct_coeff
    intro x _hx j
    exact lpsOriginalClearedAffineCusp_integral_coeff
      (N^2) (m x) (hm x).ne' (r x) j
  · intro σ
    let q := Function.Periodic.qParam 1 (σ:ℂ)
    let τ := lpsE2AffineMatrix N hN 0 • σ
    let e := lpsOriginalCuspEvaluateRingHom q
    have ha : ∀ x : I, e (A x)=q^(N^2)*
        lpsOriginalJDilated N hN (x.out.val⁻¹•τ) := by
      intro x
      change lpsOriginalClearedAffineCusp (N^2) (m x) (r x) q=_
      rw [lpsOriginalClearedAffineCusp_pullback (N^2) (m x) (hm x) (hle x) (r x) σ]
      exact congrArg (q^(N^2)* ·) (hr x σ).symm
    let f := (Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ))
    have hdegree : (Φ.map f).natDegree=Nat.card I := by
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _
        (by rw [hΦ.leadingCoeff,map_one];exact one_ne_zero),hd]
    have hscale := congrArg (fun P : Polynomial ℂ => P.scaleRoots (q^(N^2))) (hp τ)
    rw [lpsOriginalScaleRootsCosetProduct] at hscale
    have hS : S.map e=(Φ.map f).scaleRoots (q^(N^2)) := by
      rw [hscale]
      simp only [S,Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro x _hx
      rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,ha]
      rw [mul_comm (q^(N^2))]
    have hc := congrArg (fun P : Polynomial ℂ=>P.coeff k) hS
    rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,hdegree,Polynomial.coeff_map] at hc
    change G.val q=((Φ.coeff k).map (algebraMap ℚ ℂ)).eval
      (lpsOriginalJInvariant τ)*(q^(N^2))^(Nat.card I-k) at hc
    rw [←pow_mul] at hc
    exact hc.trans (mul_comm _ _)
end QEC.Coding.TannerLiftedProduct
