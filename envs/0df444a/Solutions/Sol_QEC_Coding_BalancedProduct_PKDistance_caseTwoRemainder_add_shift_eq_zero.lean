-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.caseTwoRemainder_add_shift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:55.15818+00:00
-- url     : https://prove2.me/submissions/d5401d35-e1e5-4ddf-a724-653882e9fa21

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicShift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_horizontalPart_eq_cyclicDifference_verticalPart

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
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h) :
    caseTwoRemainder A z h + cyclicShift x (caseTwoRemainder A z h) = 0 := by
  have heq :=
    tannerAction_horizontalPart_eq_cyclicDifference_verticalPart A x z hz
  rw [hu, map_add, tannerAction_cyclicShift] at heq
  rw [caseTwoRemainder, map_add]
  calc
    (verticalPart z + tannerAction A h) +
        (cyclicShift x (verticalPart z) +
          cyclicShift x (tannerAction A h)) =
      (verticalPart z + cyclicShift x (verticalPart z)) +
        (tannerAction A h + cyclicShift x (tannerAction A h)) := by
          module
    _ = (tannerAction A h + cyclicShift x (tannerAction A h)) +
        (tannerAction A h + cyclicShift x (tannerAction A h)) := by
      rw [← heq]
    _ = 0 := binaryWord_add_self _
end QEC.Coding.BalancedProduct.PKDistance
