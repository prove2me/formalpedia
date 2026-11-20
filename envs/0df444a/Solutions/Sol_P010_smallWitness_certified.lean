-- Prove2me | solution 1 for P010.smallWitness_certified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:42:38.121474+00:00
-- url     : https://prove2.me/submissions/d7a0b976-c1f6-413b-ba0a-b5661b2f1cf4

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (hnpos : 1 ≤ n) (hnmax : n ≤ 11) :
    IsPermutation n (smallWitness n) ∧
      adjacentCount (smallWitness n) =
        (if n ≤ 3 then n - 1 else target n) := by
  interval_cases n <;> (unfold IsPermutation; decide)
end P010
