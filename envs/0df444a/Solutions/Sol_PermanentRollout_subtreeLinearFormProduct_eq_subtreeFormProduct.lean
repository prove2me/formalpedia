-- Prove2me | solution 1 for PermanentRollout.subtreeLinearFormProduct_eq_subtreeFormProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/ed3bfc45-84a6-422e-ac98-69a8bd1c0cb3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_rootOfUnity_node_product_source_algebra

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R ι : Type*} [CommRing R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (hd : 0 < d) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (tree : BlockTree ι) :
    subtreeLinearFormProduct y t d ζ tree =
      subtreeFormProduct y t d
        (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree := by
  induction tree with
  | leaf i => rfl
  | branch left right ih_left ih_right =>
      simp only [subtreeLinearFormProduct, subtreeFormProduct]
      rw [ih_left, ih_right,
        rootOfUnity_node_product_source_algebra hd hζ]
end PermanentRollout
