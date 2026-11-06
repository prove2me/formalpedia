-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:39:25.284454+00:00
-- url     : https://prove2.me/submissions/93f2c636-652b-4bc5-a775-3e67649b661e

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.FreeOrbitCoordinates
universe u v
variable (G : Type u) (X : Type v) [Group G] [MulAction G X]
namespace QEC.Coding.BalancedProduct.FreeOrbitCoordinates
theorem _root_.solution [IsCancelSMul G X] (x : X) :
    freeOrbitEquiv G X x = (orbitOf G X x, groupCoordinate G X x) := rfl
end QEC.Coding.BalancedProduct.FreeOrbitCoordinates
