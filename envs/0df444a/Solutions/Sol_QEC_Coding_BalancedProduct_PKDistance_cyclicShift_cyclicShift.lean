-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.cyclicShift_cyclicShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:59:28.509639+00:00
-- url     : https://prove2.me/submissions/f2743d4e-8014-407a-b952-9015e7988398

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    (s t : G) (z : Word (ZMod 2) (I × G)) :
    cyclicShift s (cyclicShift t z) = cyclicShift (t * s) z := by
  ext p
  rcases p with ⟨i, g⟩
  change z (i, (g * s⁻¹) * t⁻¹) = z (i, g * (t * s)⁻¹)
  rw [mul_inv_rev]
  rw [mul_assoc]
end QEC.Coding.BalancedProduct.PKDistance
