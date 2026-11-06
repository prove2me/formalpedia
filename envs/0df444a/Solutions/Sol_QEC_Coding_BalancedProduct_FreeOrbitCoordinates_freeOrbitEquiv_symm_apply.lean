-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:39:34.974655+00:00
-- url     : https://prove2.me/submissions/6b97cd95-d342-407f-aeeb-75ad412daac5

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.FreeOrbitCoordinates
universe u v
variable (G : Type u) (X : Type v) [Group G] [MulAction G X]
namespace QEC.Coding.BalancedProduct.FreeOrbitCoordinates
theorem _root_.solution [IsCancelSMul G X]
    (o : OrbitIndex G X) (g : G) :
    (freeOrbitEquiv G X).symm (o, g) = g • orbitRep G X o := rfl
end QEC.Coding.BalancedProduct.FreeOrbitCoordinates
