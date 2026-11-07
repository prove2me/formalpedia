-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.fibreWeight_cyclicShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:12:59.6491+00:00
-- url     : https://prove2.me/submissions/cbb29ffa-3909-4070-8ac9-a406d24a022e

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
    {I : Type u} {G : Type v} [Group G] [Fintype G]
    (t : G) (z : Word (ZMod 2) (I × G)) (i : I) :
    fibreWeight (cyclicShift t z) i = fibreWeight z i := by
  let e : G ≃ G := Equiv.mulRight t⁻¹
  exact HammingWeight_precomp_equiv e (fun g => z (i, g))
end QEC.Coding.BalancedProduct.PKDistance
