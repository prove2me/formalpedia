-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.sum_shift_indicator_eq_fibreWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:05.853825+00:00
-- url     : https://prove2.me/submissions/29c715ac-41d4-404d-9aa7-d0b3ede9182c

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
    {I : Type u} {G : Type v} [Group G]
    [Fintype G] (z : Word (ZMod 2) (I × G)) (i : I) (g : G) :
    (∑ t, if z (i, g * t⁻¹) ≠ 0 then 1 else 0) = fibreWeight z i := by
  classical
  rw [fibreWeight, HammingWeight_eq_sum_indicator]
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft g)
  exact Fintype.sum_equiv e
    (fun t => if z (i, g * t⁻¹) ≠ 0 then 1 else 0)
    (fun x => if z (i, x) ≠ 0 then 1 else 0) (fun t => by rfl)
end QEC.Coding.BalancedProduct.PKDistance
