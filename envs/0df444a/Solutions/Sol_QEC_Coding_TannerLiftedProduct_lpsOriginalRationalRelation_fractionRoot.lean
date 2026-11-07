-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRelation_fractionRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:09:37.171491+00:00
-- url     : https://prove2.me/submissions/af9c4d1a-ab2e-43c9-970e-73ffdb11ed37

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (Φ : Polynomial (Polynomial ℚ))
    (hroot : ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval (lpsOriginalJNInFractionField N hN)
      (Φ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))=0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [Polynomial.aeval_def,Polynomial.eval₂_map]
  have hc : (algebraMap (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField).comp
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))=
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalQ := by
    apply RingHom.ext
    intro Q
    exact lpsOriginalJFractionEmbeddingQ_polynomial Q
  rw [hc]
  have hzero : Φ.eval₂ lpsOriginalJHolomorphicEvalQ
      (lpsOriginalJNHolomorphic N hN)=0 := by
    apply Subtype.ext
    funext τ
    let e : LPSOriginalHolomorphicRing →+* ℂ :=
      { toFun f := f.val τ
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl }
    have hj : e.comp lpsOriginalJHolomorphicEvalQ=
        ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ))) := by
      apply RingHom.ext
      intro Q
      change (lpsOriginalJHolomorphicEvalQ Q).val τ=
        (Q.map (algebraMap ℚ ℂ)).eval (lpsOriginalJInvariant τ)
      rw [Polynomial.eval_map]
      exact lpsOriginalJHolomorphicEvalQ_apply Q τ
    have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEvalQ e
      (lpsOriginalJNHolomorphic N hN)
    rw [hj] at h
    exact h.trans (hroot τ)
  have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEvalQ
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (lpsOriginalJNHolomorphic N hN)
  rw [hzero,map_zero] at h
  exact h.symm
end QEC.Coding.TannerLiftedProduct
