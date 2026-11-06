-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_swapWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:48.970668+00:00
-- url     : https://prove2.me/submissions/51cd6afe-3bc4-44d5-9d8d-ee403d3e1b9f

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v
namespace QEC.Coding.BalancedProduct.LiftedProductDuality
theorem _root_.solution {F A B : Type*} (z : Word F (Sum A B)) :
    swapWord (swapWord z) = z := by
  funext q
  cases q <;> rfl
end QEC.Coding.BalancedProduct.LiftedProductDuality
