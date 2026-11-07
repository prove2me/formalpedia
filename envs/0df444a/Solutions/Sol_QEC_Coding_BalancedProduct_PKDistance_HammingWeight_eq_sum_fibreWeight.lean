-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_sum_fibreWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:04.152222+00:00
-- url     : https://prove2.me/submissions/9c3d33c2-8ea4-4ed7-8a79-7520c45e5d9c

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_eq_sum_indicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight z = ∑ i, fibreWeight z i := by
  classical
  rw [HammingWeight_eq_sum_indicator]
  simp_rw [fibreWeight, HammingWeight_eq_sum_indicator]
  exact Fintype.sum_prod_type _
end QEC.Coding.BalancedProduct.PKDistance
