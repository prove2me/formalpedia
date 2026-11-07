-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNHolomorphic_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:24:15.154107+00:00
-- url     : https://prove2.me/submissions/1ed3ebcf-1751-419d-ab2f-51a2c1b02210

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_monic_relation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalJHolomorphicEval.toRingHom.IsIntegralElem
      (lpsOriginalJNHolomorphic N hN) := by
  obtain ⟨Φ,hΦ,_,hroot⟩ := lpsOriginalJ_jN_monic_relation N hN
  refine ⟨Φ,hΦ,?_⟩
  apply Subtype.ext
  funext τ
  let e : LPSOriginalHolomorphicRing →+*ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEval.toRingHom=
      Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
    apply RingHom.ext
    intro P
    exact lpsOriginalJHolomorphicEval_apply P τ
  have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEval.toRingHom e
    (lpsOriginalJNHolomorphic N hN)
  rw [hc] at h
  exact h.trans (hroot τ)
end QEC.Coding.TannerLiftedProduct
