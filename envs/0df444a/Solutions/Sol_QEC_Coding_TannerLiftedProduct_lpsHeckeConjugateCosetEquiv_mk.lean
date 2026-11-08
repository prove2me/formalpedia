-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCosetEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:07:09.020197+00:00
-- url     : https://prove2.me/submissions/952aa99b-b52a-4f96-ac84-650dffedfb00

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsHeckeConjugateCosetEquiv N p hNp (QuotientGroup.mk γ) =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
        ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property)
        (some ⟨0,(Fact.out:p.Prime).pos⟩) := by
  rfl
end QEC.Coding.TannerLiftedProduct
