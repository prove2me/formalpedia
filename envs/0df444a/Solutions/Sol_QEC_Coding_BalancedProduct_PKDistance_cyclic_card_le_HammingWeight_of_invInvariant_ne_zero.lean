-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_of_invInvariant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:53.953304+00:00
-- url     : https://prove2.me/submissions/b207b20c-a547-49fc-9eb5-f86869c92e5f

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicShift_one
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicShift_cyclicShift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_eq_cyclicShift_of_add_shift_eq_zero
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclic_card_le_HammingWeight_of_invariant_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ z = 0)
    (hne : z ≠ 0) :
    q ≤ HammingWeight z := by
  have hInvFixed : z = cyclicShift (Cyclic.cyclicGenerator q)⁻¹ z :=
    eq_cyclicShift_of_add_shift_eq_zero
      (Cyclic.cyclicGenerator q)⁻¹ z hzero
  have hForwardFixed : cyclicShift (Cyclic.cyclicGenerator q) z = z := by
    calc
      cyclicShift (Cyclic.cyclicGenerator q) z =
          cyclicShift (Cyclic.cyclicGenerator q)
            (cyclicShift (Cyclic.cyclicGenerator q)⁻¹ z) := by rw [← hInvFixed]
      _ = cyclicShift
          ((Cyclic.cyclicGenerator q)⁻¹ * Cyclic.cyclicGenerator q) z := by
        rw [cyclicShift_cyclicShift]
      _ = z := by rw [inv_mul_cancel, cyclicShift_one]
  have hForwardZero :
      z + cyclicShift (Cyclic.cyclicGenerator q) z = 0 := by
    rw [hForwardFixed, binaryWord_add_self]
  exact cyclic_card_le_HammingWeight_of_invariant_ne_zero
    q z hForwardZero hne
end QEC.Coding.BalancedProduct.PKDistance
