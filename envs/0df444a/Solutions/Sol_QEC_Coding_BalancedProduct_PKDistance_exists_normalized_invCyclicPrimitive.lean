-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.exists_normalized_invCyclicPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:06.821685+00:00
-- url     : https://prove2.me/submissions/24aca1d5-1b36-4281-8a5f-fc76d3322c9e

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_fibreWeight_cyclicShift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicShift_one
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicShift_cyclicShift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_normalized_cyclicPrimitive

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : fibreSum z = 0) :
    ∃ h : Word (ZMod 2) (I × Cyclic.CyclicGroup q),
      z = h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹) h ∧
      ∀ i, 2 * fibreWeight h i ≤ q := by
  obtain ⟨h, hz, hhalf⟩ := exists_normalized_cyclicPrimitive q hq z hzero
  refine ⟨cyclicShift (Cyclic.cyclicGenerator q) h, ?_, ?_⟩
  · rw [cyclicShift_cyclicShift, mul_inv_cancel, cyclicShift_one, add_comm]
    exact hz
  · intro i
    rw [fibreWeight_cyclicShift]
    exact hhalf i
end QEC.Coding.BalancedProduct.PKDistance
