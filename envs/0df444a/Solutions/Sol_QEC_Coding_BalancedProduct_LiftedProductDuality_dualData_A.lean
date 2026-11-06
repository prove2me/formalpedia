-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:36.351936+00:00
-- url     : https://prove2.me/submissions/dbc914d0-8578-43c6-b2e1-f154107cfa1f

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
    (dualData D).A = LiftedProduct.starTranspose D.A := rfl
end QEC.Coding.BalancedProduct.LiftedProductDuality
