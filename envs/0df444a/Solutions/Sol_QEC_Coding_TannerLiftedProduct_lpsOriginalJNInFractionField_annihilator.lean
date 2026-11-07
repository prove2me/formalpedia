-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:34:56.692889+00:00
-- url     : https://prove2.me/submissions/ab39291e-fb03-40c4-bc5d-40bdb0a77a01

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_monic_relation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∃ P : Polynomial (FractionRing (Polynomial ℂ)), P.Monic ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P=0 := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  obtain ⟨Φ,hΦ,hdeg,hroot⟩ := lpsOriginalJ_jN_monic_relation N hN
  let P := Φ.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  refine ⟨P,hΦ.map _,Polynomial.natDegree_map_le.trans hdeg.le,?_⟩
  rw [Polynomial.aeval_def,Polynomial.eval₂_map]
  have hc : (algebraMap (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))=
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEval.toRingHom := by
    apply RingHom.ext
    intro Q
    exact lpsOriginalJFractionEmbedding_polynomial Q
  rw [hc]
  have hzero : Φ.eval₂ lpsOriginalJHolomorphicEval.toRingHom
      (lpsOriginalJNHolomorphic N hN)=0 := by
    apply Subtype.ext
    funext τ
    let e : LPSOriginalHolomorphicRing →+*ℂ :=
      { toFun f := f.val τ
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl }
    have hj : e.comp lpsOriginalJHolomorphicEval.toRingHom=
        Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
      apply RingHom.ext
      intro Q
      exact lpsOriginalJHolomorphicEval_apply Q τ
    have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEval.toRingHom e
      (lpsOriginalJNHolomorphic N hN)
    rw [hj] at h
    exact h.trans (hroot τ)
  have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEval.toRingHom
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (lpsOriginalJNHolomorphic N hN)
  rw [hzero,map_zero] at h
  exact h.symm
end QEC.Coding.TannerLiftedProduct
