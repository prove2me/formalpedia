-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPrimitivePhase_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:15:34.103643+00:00
-- url     : https://prove2.me/submissions/4fce63de-7013-488e-9b77-7c92c08a1554

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0 < N) :
    IsPrimitiveRoot (lpsOriginalLevelPrimitivePhase N hN) N := by
  apply IsPrimitiveRoot.of_map_of_injective
    (f := (lpsOriginalLevelPhaseRing N).val)
    (hf := Subtype.coe_injective)
  exact Complex.isPrimitiveRoot_exp N hN.ne'
end QEC.Coding.TannerLiftedProduct
