-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:14:30.283399+00:00
-- url     : https://prove2.me/submissions/b64a6ced-f490-4d09-b76f-e0811055b92d

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {P : alpha → Prop} [DecidablePred P] {weight : alpha → Nat}
    {x : alpha} (hx : P x) :
    finitePredicateMinimum P weight ≤ (weight x : WithTop Nat) := by
  exact (Finset.inf_le (f := fun y => if P y then (weight y : WithTop Nat) else ⊤)
    (Finset.mem_univ x)).trans_eq (if_pos hx)
end QEC.Coding.HypergraphProduct
