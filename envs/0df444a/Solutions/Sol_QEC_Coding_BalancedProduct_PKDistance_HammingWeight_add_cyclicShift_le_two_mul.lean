-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.HammingWeight_add_cyclicShift_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:05:11.342761+00:00
-- url     : https://prove2.me/submissions/6c1b30ba-c0eb-4d20-9cfa-1752d66412bf

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_cyclicShift
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight (z + cyclicShift t z) ≤ 2 * HammingWeight z := by
  calc
    HammingWeight (z + cyclicShift t z) ≤
        HammingWeight z + HammingWeight (cyclicShift t z) :=
      HammingWeight_add_le z (cyclicShift t z)
    _ = HammingWeight z + HammingWeight z := by
      rw [HammingWeight_cyclicShift]
    _ = 2 * HammingWeight z := by omega
end QEC.Coding.BalancedProduct.PKDistance
