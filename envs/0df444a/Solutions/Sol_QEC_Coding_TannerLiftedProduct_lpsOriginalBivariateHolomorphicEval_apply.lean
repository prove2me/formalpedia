-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalBivariateHolomorphicEval_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:16:49.066199+00:00
-- url     : https://prove2.me/submissions/12837e8c-4800-49ee-979c-335461d26240

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (M : ℕ) (hM : 0 < M) (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    (lpsOriginalBivariateHolomorphicEval M hM P).val τ =
      P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated M hM τ) := by
  let ev : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : ev.comp lpsOriginalJHolomorphicEval.toRingHom =
      Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
    apply RingHom.ext
    intro Q
    exact lpsOriginalJHolomorphicEval_apply Q τ
  have h := Polynomial.hom_eval₂ P lpsOriginalJHolomorphicEval.toRingHom ev
    (lpsOriginalJNHolomorphic M hM)
  rw [hc] at h
  exact h
end QEC.Coding.TannerLiftedProduct
