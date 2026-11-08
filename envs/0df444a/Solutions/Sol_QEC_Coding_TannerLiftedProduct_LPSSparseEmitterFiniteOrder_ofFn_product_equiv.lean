-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_product_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:04:26.392957+00:00
-- url     : https://prove2.me/submissions/8a516042-5c32-43c7-8ae1-96e86763efb1

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFiniteOrder_ofFn_product

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
theorem _root_.solution {α A B:Type*} {m n:ℕ} (ea:A≃Fin m) (eb:B≃Fin n) (f:A×B→α):
 (List.ofFn fun i:Fin (m*n)=>f (((Equiv.prodCongr ea eb).trans finProdFinEquiv).symm i))=
 (List.ofFn fun i:Fin m=>List.ofFn fun j:Fin n=>f (ea.symm i,eb.symm j)).flatten:=by
 have h:=ofFn_product (fun x:Fin m×Fin n=>f (ea.symm x.1,eb.symm x.2))
 exact h
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
