-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:27.622278+00:00
-- url     : https://prove2.me/submissions/f34c8edb-4e02-4e25-9888-fb7789446e62

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v
namespace QEC.Coding.BalancedProduct.LiftedProductDuality
theorem _root_.solution
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : LiftedProduct.Data F G aRow aCol bRow bCol) :
    (dualData D).B = LiftedProduct.starTranspose D.B := rfl
end QEC.Coding.BalancedProduct.LiftedProductDuality
