-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicPrefix_horizontalPart_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:03.577898+00:00
-- url     : https://prove2.me/submissions/005d3d21-bf4a-4fbf-8046-322490050504

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicPrefix
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_horizontalPart_eq_cyclicDifference_verticalPart
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_cyclicDifference

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0)
    (t : Nat) :
    tannerAction A (cyclicPrefix x t (horizontalPart z)) =
      verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by
  rw [tannerAction_cyclicPrefix,
    tannerAction_horizontalPart_eq_cyclicDifference_verticalPart A x z hz,
    cyclicPrefix_cyclicDifference]
end QEC.Coding.BalancedProduct.PKDistance
