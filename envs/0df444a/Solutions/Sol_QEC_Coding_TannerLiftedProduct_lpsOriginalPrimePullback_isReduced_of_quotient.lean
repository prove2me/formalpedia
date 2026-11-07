-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimePullback_isReduced_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:40.275038+00:00
-- url     : https://prove2.me/submissions/e5cf152f-2239-440b-a920-d4d4f484525d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_tensorPrime_isReduced_of_quotient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSpecZ_hom_unique


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (C : Type) [CommRing C] (p : ℕ) [Fact p.Prime]
    (h : _root_.IsReduced (C ⧸ Ideal.span {(p : C)}))
    (f : Spec (.of C) ⟶ Spec (.of ℤ)) :
    _root_.AlgebraicGeometry.IsReduced (pullback f (lpsOriginalPrimeSpecToInteger p)) := by
  let := h
  let : _root_.IsReduced (C ⊗[ℤ] ZMod p) :=
    QEC.Coding.AlgebraicGeometry.tensorPrime_isReduced_of_quotient C p
  have hf : f = Spec.map (CommRingCat.ofHom (algebraMap ℤ C)) :=
    lpsOriginalIntegerSpecZ_hom_unique C _ _
  let e := (pullback.congrHom hf (rfl : lpsOriginalPrimeSpecToInteger p =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))))) ≪≫ pullbackSpecIso ℤ C (ZMod p)
  exact isReduced_of_isOpenImmersion e.hom
end QEC.Coding.TannerLiftedProduct
