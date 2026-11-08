-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder.ofFn_sum_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:29:32.285947+00:00
-- url     : https://prove2.me/submissions/c57b543a-b226-4d5c-9f1f-e35c91e2b46b

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFiniteOrder_ofFn_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
theorem _root_.solution {α A B:Type*} {m n:ℕ} (ea:A≃Fin m) (eb:B≃Fin n) (f:A⊕B→α):
 (List.ofFn fun i:Fin (m+n)=>f (((Equiv.sumCongr ea eb).trans finSumFinEquiv).symm i))=
 (List.ofFn fun i:Fin m=>f (Sum.inl (ea.symm i)))++(List.ofFn fun i:Fin n=>f (Sum.inr (eb.symm i))):=by
 have h:=ofFn_sum (fun x:Fin m⊕Fin n=>f ((Equiv.sumCongr ea eb).symm x))
 exact h
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFiniteOrder
