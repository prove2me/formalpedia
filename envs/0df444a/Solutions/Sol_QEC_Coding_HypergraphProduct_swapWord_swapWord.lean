-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.swapWord_swapWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:32:55.164202+00:00
-- url     : https://prove2.me/submissions/da99d06f-a917-4687-85b6-972fe7a37322

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution {F A B : Type*} (x : Word F (Sum A B)) :
    swapWord (swapWord x) = x := by
  funext q
  cases q <;> rfl
end QEC.Coding.HypergraphProduct
