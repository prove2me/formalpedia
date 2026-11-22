-- Prove2me | solution 1 for PebblingLean.Graph.adj_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:03.306803+00:00
-- url     : https://prove2.me/submissions/62c9dfa4-fc90-48ce-a524-06a60c2e73b0

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Graph
variable {V : Type u} (G : Graph V)
namespace PebblingLean.Graph
theorem _root_.solution {u v : V} : G.Adj u v ↔ G.Adj v u :=
  ⟨G.symm, G.symm⟩
end PebblingLean.Graph
