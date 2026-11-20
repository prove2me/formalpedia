-- Prove2me | solution 1 for P010.join_even_ended_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:42:44.02643+00:00
-- url     : https://prove2.me/submissions/c4b5b7f1-42fd-4e28-96ee-7b3ac5a48525

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_join_prime_ended_paths

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (a b : List ℕ)
    (ha : NonCoprimeChain a) (hb : NonCoprimeChain b)
    (hend : ∀ x : ℕ, x ∈ a.getLast? → 2 ∣ x)
    (hstart : ∀ y : ℕ, y ∈ b.head? → 2 ∣ y) :
    NonCoprimeChain (a ++ b) := by
  exact join_prime_ended_paths 2 (by norm_num) a b ha hb hend hstart
end P010
