-- Prove2me | solution 1 for P010.isolated_path_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:45:52.846062+00:00
-- url     : https://prove2.me/submissions/fc948680-3957-47d6-b67a-507b4394ca12

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_large_prime_path_singleton
public import Theorems.Thm_P010_one_path_singleton

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (a : List ℕ)
    (hi : p ∈ isolatedVertices n) (hc : NonCoprimeChain a)
    (hd : a.Nodup) (hp : p ∈ a)
    (hb : ∀ t ∈ a, 0 < t ∧ t ≤ n) : a = [p] := by
  rcases Finset.mem_insert.mp hi with h1 | hl
  · subst p
    exact one_path_singleton a hc hd hp
  · exact large_prime_path_singleton n p a hl hc hd hp hb
end P010
