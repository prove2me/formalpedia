-- Prove2me | solution 1 for P010.h_le_of_noncoprime_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:46:42.821389+00:00
-- url     : https://prove2.me/submissions/cd031e6d-c9e8-408d-8f43-871e3c80c1fb

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_h_le_of_permutation
public import Theorems.Thm_P010_adjacentCount_flatten_le

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (paths : List (List ℕ))
    (hcover : IsPermutation n paths.flatten)
    (hpaths : ∀ p ∈ paths, NonCoprimeChain p) :
    h n ≤ paths.length - 1 := by
  exact (h_le_of_permutation n paths.flatten hcover).trans
    (adjacentCount_flatten_le paths hpaths)
end P010
