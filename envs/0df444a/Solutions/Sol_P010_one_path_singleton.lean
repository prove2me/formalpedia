-- Prove2me | solution 1 for P010.one_path_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:01.791187+00:00
-- url     : https://prove2.me/submissions/02c2e02b-02be-40d1-8d40-13af449e6132

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_one_coprime
public import Theorems.Thm_P010_isolated_member_forces_singleton

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (a : List ℕ)
    (hchain : NonCoprimeChain a) (hnodup : a.Nodup)
    (hmem : 1 ∈ a) : a = [1] := by
  apply isolated_member_forces_singleton 1 a hchain hnodup hmem
  intro x _ _
  exact one_coprime x
end P010
