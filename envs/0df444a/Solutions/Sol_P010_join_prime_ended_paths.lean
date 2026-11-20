-- Prove2me | solution 1 for P010.join_prime_ended_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:30:02.425418+00:00
-- url     : https://prove2.me/submissions/21281348-46b3-45d0-b084-7f972334123b

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
theorem _root_.solution (p : ℕ) (hp : Nat.Prime p)
    (a b : List ℕ)
    (ha : NonCoprimeChain a) (hb : NonCoprimeChain b)
    (hend : ∀ x : ℕ, x ∈ a.getLast? → p ∣ x)
    (hstart : ∀ y : ℕ, y ∈ b.head? → p ∣ y) :
    NonCoprimeChain (a ++ b) := by
  exact List.IsChain.append ha hb (fun x hx y hy =>
    common_prime_divisor_noncoprime hp (hend x hx) (hstart y hy))
end P010
