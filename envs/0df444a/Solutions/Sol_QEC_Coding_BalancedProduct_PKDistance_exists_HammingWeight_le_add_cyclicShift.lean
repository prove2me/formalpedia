-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.exists_HammingWeight_le_add_cyclicShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:29:04.333105+00:00
-- url     : https://prove2.me/submissions/2cc8f7db-df8a-4738-afae-522d05b3a07f

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_cyclicShift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_add_add_two_mul_binaryOverlap
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_two_mul_binaryOverlap_cyclicShift_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ Fintype.card G) :
    ∃ t : G, HammingWeight z ≤ HammingWeight (z + cyclicShift t z) := by
  obtain ⟨t, hoverlap⟩ :=
    exists_two_mul_binaryOverlap_cyclicShift_le z hhalf
  refine ⟨t, ?_⟩
  have hxor := HammingWeight_add_add_two_mul_binaryOverlap
    z (cyclicShift t z)
  rw [HammingWeight_cyclicShift] at hxor
  omega
end QEC.Coding.BalancedProduct.PKDistance
