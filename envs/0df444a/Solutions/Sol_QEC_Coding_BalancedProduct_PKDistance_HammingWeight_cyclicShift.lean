-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:02:02.322607+00:00
-- url     : https://prove2.me/submissions/3b157e30-f22d-4637-9cb2-a0017ac3055d

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_precomp_equiv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight (cyclicShift t z) = HammingWeight z := by
  let e : I × G ≃ I × G :=
    (Equiv.refl I).prodCongr (Equiv.mulRight t⁻¹)
  exact HammingWeight_precomp_equiv e z
end QEC.Coding.BalancedProduct.PKDistance
