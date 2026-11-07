-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.swapWord_inl_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:32:54.244199+00:00
-- url     : https://prove2.me/submissions/218a210b-56da-4263-b228-c87a39334f3a

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution {F A B : Type*} (x : Word F (Sum A B)) (b : B) :
    swapWord x (Sum.inl b) = x (Sum.inr b) := rfl
end QEC.Coding.HypergraphProduct
