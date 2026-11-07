-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.exists_caseTwo_cyclicDifference_before_crossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:37:40.178205+00:00
-- url     : https://prove2.me/submissions/e8de8297-b5ca-4380-8d97-14464a3e61d0

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_cyclicPower_HammingWeight_le_add_shift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_weight_before_first_crossing
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_cyclicPrefix_step
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicShift_one
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_cyclicDifference

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (h : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold : Nat) (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h) :
    ∃ t < q,
      HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h) < threshold ∧
      threshold ≤ HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q ^ (t + 1)) h) ∧
      threshold ≤
        HammingWeight (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h) +
          HammingWeight (h + cyclicShift (Cyclic.cyclicGenerator q) h) := by
  obtain ⟨last, hlastq, hlast⟩ :=
    exists_cyclicPower_HammingWeight_le_add_shift q h hhalf
  let sequence : Nat → Word (ZMod 2) (I × Cyclic.CyclicGroup q) :=
    fun t => h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h
  have hstart : HammingWeight (sequence 0) < threshold := by
    change HammingWeight
      (h + cyclicShift (Cyclic.cyclicGenerator q ^ 0) h) < threshold
    rw [pow_zero, cyclicShift_one, binaryWord_add_self, HammingWeight_zero]
    exact hthreshold
  have hend : threshold ≤ HammingWeight (sequence last) :=
    hPrimitive.trans hlast
  have hstep : ∀ t < last,
      HammingWeight (sequence (t + 1) + sequence t) ≤
        HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q) h) := by
    intro t _ht
    change HammingWeight
      ((h + cyclicShift (Cyclic.cyclicGenerator q ^ (t + 1)) h) +
        (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h)) ≤ _
    rw [← cyclicPrefix_cyclicDifference
        (Cyclic.cyclicGenerator q) (t + 1) h,
      ← cyclicPrefix_cyclicDifference (Cyclic.cyclicGenerator q) t h,
      HammingWeight_cyclicPrefix_step]
  obtain ⟨t, htlast, htbelow, htabove, htnear⟩ :=
    exists_weight_before_first_crossing sequence last threshold
      (HammingWeight
        (h + cyclicShift (Cyclic.cyclicGenerator q) h))
      hstart hend hstep
  exact ⟨t, htlast.trans hlastq, htbelow, htabove, htnear⟩
end QEC.Coding.BalancedProduct.PKDistance
