-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.swapWord_inr_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:06.399239+00:00
-- url     : https://prove2.me/submissions/a4e54362-f621-46e5-ba1c-9cc793b49922

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution {F A B : Type*} (x : Word F (Sum A B)) (a : A) :
    swapWord x (Sum.inr a) = x (Sum.inl a) := rfl
end QEC.Coding.HypergraphProduct
