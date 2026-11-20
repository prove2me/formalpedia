-- Prove2me | solution 1 for P010.join_three_ended_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:35:52.786905+00:00
-- url     : https://prove2.me/submissions/53b4d8f2-35d3-4d84-ab05-9effa0d3df34

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
    (hend : ∀ x : ℕ, x ∈ a.getLast? → 3 ∣ x)
    (hstart : ∀ y : ℕ, y ∈ b.head? → 3 ∣ y) :
    NonCoprimeChain (a ++ b) := by
  exact join_prime_ended_paths 3 (by norm_num) a b ha hb hend hstart
end P010
