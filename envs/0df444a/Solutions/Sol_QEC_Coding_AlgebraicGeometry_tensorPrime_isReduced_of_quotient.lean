-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.tensorPrime_isReduced_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:33:41.643169+00:00
-- url     : https://prove2.me/submissions/6258dca5-3354-4a03-bfe0-f29d5f4b9bed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
open scoped TensorProduct
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (C : Type) [CommRing C] (p : ℕ)
    [IsReduced (C ⧸ Ideal.span {(p : C)})] : IsReduced (C ⊗[ℤ] ZMod p) := by
  let e := quotientPrimeTensorEquiv C p
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective
end QEC.Coding.AlgebraicGeometry
