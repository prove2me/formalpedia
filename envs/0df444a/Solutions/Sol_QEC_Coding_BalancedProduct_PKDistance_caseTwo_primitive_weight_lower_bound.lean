-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.caseTwo_primitive_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:25:41.288765+00:00
-- url     : https://prove2.me/submissions/848435c1-c864-4ab4-abb7-da508fb93e5e

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclic_card_le_HammingWeight_caseTwoRemainder
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
import Theorems.Thm_QEC_Coding_HammingWeight_linearMap_le_of_basis


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1 (Cyclic.data q A) z = 0)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q) h)
    (w : Nat)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w) :
    q ≤ HammingWeight (verticalPart z) + w * HammingWeight h := by
  have hRemainder := cyclic_card_le_HammingWeight_caseTwoRemainder
    q A z hz hzNotBoundary h hu
  have hTriangle : HammingWeight (caseTwoRemainder A z h) ≤
      HammingWeight (verticalPart z) + HammingWeight (tannerAction A h) := by
    exact HammingWeight_add_le (verticalPart z) (tannerAction A h)
  have hTanner : HammingWeight (tannerAction A h) ≤ w * HammingWeight h :=
    HammingWeight_linearMap_le_of_basis (tannerAction A) w hColumnWeight h
  exact hRemainder.trans
    (hTriangle.trans (Nat.add_le_add_left hTanner _))
end QEC.Coding.BalancedProduct.PKDistance
