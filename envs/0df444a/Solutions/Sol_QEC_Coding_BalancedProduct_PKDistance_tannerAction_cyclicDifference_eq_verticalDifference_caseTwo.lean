-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.tannerAction_cyclicDifference_eq_verticalDifference_caseTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:54.959198+00:00
-- url     : https://prove2.me/submissions/3f1215bf-0d86-4417-9deb-daae7a53f635

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicShift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_caseTwoRemainder_add_shift_eq_zero
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_eq_cyclicShift_pow_of_add_shift_eq_zero

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
    (hz : LiftedProduct.boundary1 (Cyclic.liftedProductData A x) z = 0)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h)
    (t : Nat) :
    tannerAction A (h + cyclicShift (x ^ t) h) =
      verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by
  let r := caseTwoRemainder A z h
  have hrGenerator : r + cyclicShift x r = 0 :=
    caseTwoRemainder_add_shift_eq_zero A x z hz h hu
  have hrPower : r = cyclicShift (x ^ t) r :=
    eq_cyclicShift_pow_of_add_shift_eq_zero x r hrGenerator t
  change verticalPart z + tannerAction A h =
      cyclicShift (x ^ t) (verticalPart z + tannerAction A h) at hrPower
  rw [map_add, tannerAction_cyclicShift]
  rw [map_add] at hrPower
  have hcancel :
      (verticalPart z + tannerAction A h) +
        (cyclicShift (x ^ t) (verticalPart z) +
          cyclicShift (x ^ t) (tannerAction A h)) = 0 := by
    rw [hrPower, binaryWord_add_self]
  calc
    tannerAction A h + cyclicShift (x ^ t) (tannerAction A h) =
      (verticalPart z + cyclicShift (x ^ t) (verticalPart z)) +
        ((verticalPart z + tannerAction A h) +
          (cyclicShift (x ^ t) (verticalPart z) +
            cyclicShift (x ^ t) (tannerAction A h))) := by
        calc
          tannerAction A h + cyclicShift (x ^ t) (tannerAction A h) =
            (verticalPart z + verticalPart z) +
              (cyclicShift (x ^ t) (verticalPart z) +
                cyclicShift (x ^ t) (verticalPart z)) +
              (tannerAction A h + cyclicShift (x ^ t) (tannerAction A h)) := by
            rw [binaryWord_add_self, binaryWord_add_self, zero_add, zero_add]
          _ = (verticalPart z + cyclicShift (x ^ t) (verticalPart z)) +
              ((verticalPart z + tannerAction A h) +
                (cyclicShift (x ^ t) (verticalPart z) +
                  cyclicShift (x ^ t) (tannerAction A h))) := by
            abel
    _ = verticalPart z + cyclicShift (x ^ t) (verticalPart z) := by
      rw [hcancel, add_zero]
end QEC.Coding.BalancedProduct.PKDistance
