-- Prove2me | solution 1 for PermanentRollout.treeLinearFormVectors_quotient_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/601d4fc5-23a8-4e0c-9886-c07d2c19f65e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_block
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_node

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (t d : ℕ) (ζ : ℂ) (tree : BlockTree ι) :
    ((treeLinearFormVectors blocks t d ζ tree).map
      treeQuotientLinearForm).prod =
      subtreeLinearFormProduct
        (fun i => squareZeroBlockSum r (blocks i)) t d ζ tree := by
  classical
  induction tree with
  | leaf i =>
      simp [treeLinearFormVectors, subtreeLinearFormProduct,
        treeQuotientLinearForm_block]
  | branch left right ihleft ihright =>
      simp only [treeLinearFormVectors, List.map_append,
        List.prod_append, subtreeLinearFormProduct, ihleft, ihright]
      congr 1
      rw [List.map_ofFn, List.prod_ofFn]
      simpa only [Function.comp_apply, treeQuotientLinearForm_node] using
        (Fin.prod_univ_eq_prod_range
          (fun j : ℕ =>
            (∑ i ∈ left.leaves, squareZeroBlockSum r (blocks i)) +
              algebraMap ℂ (SquareZeroAlgebra r) (2 * ζ ^ j) *
                (∑ i ∈ right.leaves, squareZeroBlockSum r (blocks i))) d)
end PermanentRollout
