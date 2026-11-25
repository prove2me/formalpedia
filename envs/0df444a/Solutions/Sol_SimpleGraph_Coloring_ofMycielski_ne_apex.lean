-- Prove2me | solution 1 for SimpleGraph.Coloring.ofMycielski_ne_apex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:00:42.118339+00:00
-- url     : https://prove2.me/submissions/179be4a5-d97c-4927-8bc9-a6552208aef3

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
namespace SimpleGraph
namespace Coloring
theorem _root_.solution (C : G.mycielski.Coloring α) (v : V) :
    C.ofMycielski v ≠ C none := by
  classical
  change (if C (some (.inl v)) = C none then C (some (.inr v))
    else C (some (.inl v))) ≠ C none
  split_ifs with h
  · exact C.valid (show G.mycielski.Adj (some (.inr v)) none from trivial)
  · exact h
end Coloring
end SimpleGraph
