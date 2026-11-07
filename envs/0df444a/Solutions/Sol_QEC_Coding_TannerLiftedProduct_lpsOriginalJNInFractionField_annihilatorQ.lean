-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_annihilatorQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:43:02.319089+00:00
-- url     : https://prove2.me/submissions/3224b8fc-5d5f-4fdd-8a1b-eccc409a60e4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_rational_monic_relation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∃ P : Polynomial (FractionRing (Polynomial ℚ)), P.Monic ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P=0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  obtain ⟨Φ,hΦ,hdeg,hroot⟩ := lpsOriginalJ_jN_rational_monic_relation N hN
  let P := Φ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
  refine ⟨P,hΦ.map _,Polynomial.natDegree_map_le.trans hdeg.le,?_⟩
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
    let e : LPSOriginalHolomorphicRing →+*ℂ :=
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
      change (lpsOriginalJHolomorphicEvalQ Q).val τ=(Q.map (algebraMap ℚ ℂ)).eval (lpsOriginalJInvariant τ)
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
