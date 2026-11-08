-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNHolomorphic_integralQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:09:23.270139+00:00
-- url     : https://prove2.me/submissions/efc6cfe9-4923-4383-8f31-887f7ec29277

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_rational_monic_relation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalJHolomorphicEvalQ.IsIntegralElem
      (lpsOriginalJNHolomorphic N hN) := by
  obtain ⟨Φ,hΦ,_,hroot⟩ := lpsOriginalJ_jN_rational_monic_relation N hN
  refine ⟨Φ,hΦ,?_⟩
  apply Subtype.ext
  funext τ
  let e : LPSOriginalHolomorphicRing →+*ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEvalQ=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) := by
    apply RingHom.ext
    intro P
    change (lpsOriginalJHolomorphicEvalQ P).val τ=(P.map (algebraMap ℚ ℂ)).eval (lpsOriginalJInvariant τ)
    rw [Polynomial.eval_map]
    exact lpsOriginalJHolomorphicEvalQ_apply P τ
  have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEvalQ e
    (lpsOriginalJNHolomorphic N hN)
  rw [hc] at h
  exact h.trans (hroot τ)
end QEC.Coding.TannerLiftedProduct
