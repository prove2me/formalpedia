-- Prove2me | solution 1 for OPG1808.induced_subtournament_reachability_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:45:41.37982+00:00
-- url     : https://prove2.me/submissions/20127f50-3310-43c9-86e0-68cae560ee96

import Mathlib

set_option autoImplicit false

/-! The target's preamble defines `OPG1808.ArcColoring` and `OPG1808.MonochromaticallyReaches`
inline (no Definitions bundle). A proof may not import its own target module, and redeclaring the
same names would clash with it, so the statement below is written against local aliases with
IDENTICAL bodies under a distinct namespace. They are definitionally equal to the target's
constants, so `solution` has the target's type up to delta-unfolding. -/
namespace OPG1808Sol

abbrev ArcColoring (V : Type) : Type := V → V → Fin 3

abbrev MonochromaticallyReaches {V : Type} (D : Digraph V) (color : ArcColoring V)
    (s t : V) (i : Fin 3) : Prop :=
  Relation.ReflTransGen (fun x y : V => D.Adj x y ∧ color x y = i) s t

end OPG1808Sol

open OPG1808Sol in
theorem solution
    {V : Type} [Fintype V]
    (D : Digraph V) (color : ArcColoring V)
    (C : Finset V) (s t : V) (i : Fin 3)
    (h : Relation.ReflTransGen
      (fun x y : V => x ∈ C ∧ y ∈ C ∧ D.Adj x y ∧ color x y = i) s t) :
    MonochromaticallyReaches D color s t i := by
  show Relation.ReflTransGen (fun x y : V => D.Adj x y ∧ color x y = i) s t
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨hbc.2.2.1, hbc.2.2.2⟩

#print axioms solution
