-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_integer_monic_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:05:09.119174+00:00
-- url     : https://prove2.me/submissions/9b015008-fb24-4176-80df-5fafaac94c19

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRelation_pointwiseProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalIntegral_isInteger
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalCosetCoefficient_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_rational_monic_relation
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
    (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Ψ : Polynomial (Polynomial ℤ), Ψ.Monic ∧
      Ψ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, Ψ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) (lpsOriginalJDilated N hN τ)=0 := by
  classical
  obtain ⟨Φ,hΦ,hd,hr⟩ := lpsOriginalJ_jN_rational_monic_relation N hN
  have hp := lpsOriginalRationalRelation_pointwiseProduct N hN Φ hΦ hd hr
  have hLift : Φ ∈ Polynomial.lifts (Polynomial.mapRingHom (algebraMap ℤ ℚ)) := by
    apply (Polynomial.lifts_iff_coeff_lifts Φ).mpr
    intro k
    apply (Polynomial.mem_lifts (Φ.coeff k)).mp
    apply (Polynomial.lifts_iff_coeff_lifts (Φ.coeff k)).mpr
    intro n
    obtain ⟨z,hz⟩ := lpsOriginalRationalIntegral_isInteger ((Φ.coeff k).coeff n)
      (lpsOriginalRationalCosetCoefficient_integral N hN Φ hΦ hd hp k n)
    refine ⟨z,?_⟩
    change (z:ℚ)=(Φ.coeff k).coeff n
    exact hz
  obtain ⟨Ψ,hΨ⟩ := (Polynomial.mem_lifts Φ).mp hLift
  have hInt : Function.Injective (algebraMap ℤ ℚ) := by
    intro z w h
    change (z:ℚ)=(w:ℚ) at h
    exact_mod_cast h
  have hf : Function.Injective (Polynomial.mapRingHom (algebraMap ℤ ℚ)) :=
    Polynomial.map_injective _ hInt
  have hmonic : Ψ.Monic := Polynomial.monic_of_injective hf (by rw [hΨ];exact hΦ)
  have hdegree : Ψ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
    rw [←Polynomial.natDegree_map_eq_of_injective hf Ψ,hΨ,hd]
  refine ⟨Ψ,hmonic,hdegree,?_⟩
  intro τ
  have hc : (((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ))).comp
      (Polynomial.mapRingHom (algebraMap ℤ ℚ)))=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change ((P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).eval
      (lpsOriginalJInvariant τ)=(P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [Polynomial.map_map]
    have he : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)=Int.castRingHom ℂ := by
      apply RingHom.ext
      intro z
      simp only [RingHom.comp_apply,algebraMap_int_eq,Int.coe_castRingHom,map_intCast]
    rw [he]
  have h := hr τ
  rw [←hΨ,Polynomial.eval₂_map,hc] at h
  exact h
end QEC.Coding.TannerLiftedProduct
