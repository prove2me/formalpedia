-- Prove2me | solution 1 for P010.h_le_of_permutation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:31:12.343624+00:00
-- url     : https://prove2.me/submissions/569ce2ea-c28c-4097-955a-1550bc74dc6a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (a : List ℕ) (ha : IsPermutation n a) :
    h n ≤ adjacentCount a := by
  classical
  exact Nat.find_min' (attainable n) ⟨a, ha, rfl⟩
end P010
