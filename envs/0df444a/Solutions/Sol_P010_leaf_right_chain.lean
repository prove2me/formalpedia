-- Prove2me | solution 1 for P010.leaf_right_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:47:54.007669+00:00
-- url     : https://prove2.me/submissions/dc4183d7-8331-49fc-83fa-cb47de4ef64e

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_common_prime_divisor_noncoprime

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (p : ℕ) (hp : Nat.Prime p) :
    NonCoprimeChain [2 * p, p] := by
  exact (List.isChain_pair).2
    (common_prime_divisor_noncoprime hp
      ⟨2, by omega⟩ (dvd_refl p))
end P010
