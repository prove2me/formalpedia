-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCosetEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:07:07.425628+00:00
-- url     : https://prove2.me/submissions/3c55483d-1eac-4d41-ac73-bf621af4aaa7

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
    lpsHeckeIntersectionCosetEquiv N p hNp (QuotientGroup.mk γ) =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
        ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property) none := by
  rfl
end QEC.Coding.TannerLiftedProduct
