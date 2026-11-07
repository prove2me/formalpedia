-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.exists_apply_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:11:52.127665+00:00
-- url     : https://prove2.me/submissions/65904629-2f46-48e7-9b1c-d9952b078407

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {A : Type u} [Zero F]
    (x : Word F A) (hx : x ≠ 0) : ∃ a, x a ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  funext a
  exact h a
end QEC.Coding.HypergraphProduct
