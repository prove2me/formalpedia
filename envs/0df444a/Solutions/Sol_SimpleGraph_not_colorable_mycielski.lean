-- Prove2me | solution 1 for SimpleGraph.not_colorable_mycielski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:07:44.650254+00:00
-- url     : https://prove2.me/submissions/c878a83b-2e86-4e4a-b07d-839db0646637

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski
public import Theorems.Thm_SimpleGraph_Coloring_ofMycielski_ne_apex

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
namespace SimpleGraph
theorem _root_.solution (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    ¬G.mycielski.Colorable k := by
  rintro ⟨C⟩
  obtain ⟨v, hv⟩ := (le_chromaticNumber_iff_forall_surjective.mp h)
    C.ofMycielski (C none)
  exact C.ofMycielski_ne_apex v hv
end SimpleGraph
