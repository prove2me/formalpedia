-- Prove2me | solution 1 for P010.leaf_left_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:47:39.795177+00:00
-- url     : https://prove2.me/submissions/0d14c3f9-146a-4018-84c8-1c18f9ca8bde

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
    NonCoprimeChain [p, 2 * p] := by
  exact (List.isChain_pair).2
    (common_prime_divisor_noncoprime hp (dvd_refl p)
      ⟨2, by omega⟩)
end P010
