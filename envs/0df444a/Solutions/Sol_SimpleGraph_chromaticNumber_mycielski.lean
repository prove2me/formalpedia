-- Prove2me | solution 1 for SimpleGraph.chromaticNumber_mycielski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:11:36.80913+00:00
-- url     : https://prove2.me/submissions/403b0558-f558-4540-bc45-6f510b1debea

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski
public import Theorems.Thm_SimpleGraph_not_colorable_mycielski

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
namespace SimpleGraph
theorem _root_.solution (h : G.chromaticNumber = (k : ℕ∞)) :
    G.mycielski.chromaticNumber = ((k + 1 : ℕ) : ℕ∞) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (chromaticNumber_eq_iff_colorable_not_colorable.mpr
      ⟨(chromaticNumber_le_iff_colorable.mp h.le).mycielski,
        not_colorable_mycielski h.ge⟩)
end SimpleGraph
