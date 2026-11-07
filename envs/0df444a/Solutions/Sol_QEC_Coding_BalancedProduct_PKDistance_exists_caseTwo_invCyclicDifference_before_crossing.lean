-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.exists_caseTwo_invCyclicDifference_before_crossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:26.019201+00:00
-- url     : https://prove2.me/submissions/cb851474-3a3d-4fd7-9684-0715ece35525

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_invCyclicPower_HammingWeight_le_add_shift
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
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) h) < threshold ∧
      threshold ≤ HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ (t + 1)) h) ∧
      threshold ≤ HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) h) +
        HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h) := by
  obtain ⟨last, hlastq, hlast⟩ :=
    exists_invCyclicPower_HammingWeight_le_add_shift q h hhalf
  let x := (Cyclic.cyclicGenerator q)⁻¹
  let sequence : Nat → Word (ZMod 2) (I × Cyclic.CyclicGroup q) :=
    fun t => h + cyclicShift (x ^ t) h
  have hstart : HammingWeight (sequence 0) < threshold := by
    change HammingWeight (h + cyclicShift (x ^ 0) h) < threshold
    rw [pow_zero, cyclicShift_one, binaryWord_add_self, HammingWeight_zero]
    exact hthreshold
  have hend : threshold ≤ HammingWeight (sequence last) :=
    hPrimitive.trans hlast
  have hstep : ∀ t < last,
      HammingWeight (sequence (t + 1) + sequence t) ≤
        HammingWeight (h + cyclicShift x h) := by
    intro t _ht
    change HammingWeight
      ((h + cyclicShift (x ^ (t + 1)) h) +
        (h + cyclicShift (x ^ t) h)) ≤ _
    rw [← cyclicPrefix_cyclicDifference x (t + 1) h,
      ← cyclicPrefix_cyclicDifference x t h,
      HammingWeight_cyclicPrefix_step]
  obtain ⟨t, htlast, htbelow, htabove, htnear⟩ :=
    exists_weight_before_first_crossing sequence last threshold
      (HammingWeight (h + cyclicShift x h)) hstart hend hstep
  exact ⟨t, htlast.trans hlastq, htbelow, htabove, htnear⟩
end QEC.Coding.BalancedProduct.PKDistance
