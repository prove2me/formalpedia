-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.Cyclic.liftedProductData_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:04:58.280884+00:00
-- url     : https://prove2.me/submissions/bebf92d0-c169-4308-9b13-7e6bd34d3a5c

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.Cyclic
theorem _root_.solution
    {G : Type u} {aRow aCol : Type v} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    (liftedProductData A x).A = A := rfl
end QEC.Coding.BalancedProduct.Cyclic
