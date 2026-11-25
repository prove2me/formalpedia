-- Prove2me | solution 1 for SimpleGraph.chromaticNumber_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:00:57.993596+00:00
-- url     : https://prove2.me/submissions/e317a84a-be31-4c0b-9172-f386c528432b

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
variable {W : Type*}
namespace SimpleGraph
theorem _root_.solution (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e).chromaticNumber = G.chromaticNumber := by
  exact le_antisymm
    (chromaticNumber_mono_of_hom (Iso.map e G).symm.toHom)
    (chromaticNumber_mono_of_hom (Iso.map e G).toHom)
end SimpleGraph
