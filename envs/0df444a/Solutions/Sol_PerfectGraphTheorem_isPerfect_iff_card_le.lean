-- Prove2me | solution 1 for PerfectGraphTheorem.isPerfect_iff_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:56:25.621804+00:00
-- url     : https://prove2.me/submissions/4767bf93-9783-4784-9112-004a1fe84339

module
public import Mathlib
public import Definitions.Def_PerfectLib_Perfect
public import Definitions.Def_PerfectGraphs_Solution
public import Theorems.Thm_PerfectGraph_isPerfect_iff_card_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraphTheorem
variable {V : Type*}
namespace PerfectGraphTheorem
theorem _root_.solution [Finite V] (G : SimpleGraph V) :
    IsPerfect G ↔ ∀ S : Finset V,
      S.card ≤ (G.induce (S : Set V)).indepNum * (G.induce (S : Set V)).cliqueNum :=
  PerfectGraph.isPerfect_iff_card_le G
end PerfectGraphTheorem
