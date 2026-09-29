-- Prove2me | solution 1 for OPG1808.source_component_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:45:41.53918+00:00
-- url     : https://prove2.me/submissions/1a3d8b8c-612e-4e0d-be1b-dd07e78548cc

import Mathlib

set_option autoImplicit false

/-! The target's preamble defines `OPG1808.ArcColoring`, `OPG1808.MonochromaticallyReaches` and
`OPG1808.IsMonochromaticSource` inline (no Definitions bundle). A proof may not import its own
target module, and redeclaring the same names would clash with it, so the statement below is
written against local aliases with IDENTICAL bodies under a distinct namespace. They are
definitionally equal to the target's constants, so `solution` has the target's type up to
delta-unfolding. -/
namespace OPG1808Sol

abbrev ArcColoring (V : Type) : Type := V → V → Fin 3

abbrev MonochromaticallyReaches {V : Type} (D : Digraph V) (color : ArcColoring V)
    (s t : V) (i : Fin 3) : Prop :=
  Relation.ReflTransGen (fun x y : V => D.Adj x y ∧ color x y = i) s t

abbrev IsMonochromaticSource {V : Type} (D : Digraph V) (color : ArcColoring V) (s : V) : Prop :=
  ∀ t : V, ∃ i : Fin 3, MonochromaticallyReaches D color s t i

end OPG1808Sol

/-- A monochromatic path staying inside `C` is a monochromatic path. -/
theorem opg1808sol_lift_path {V : Type} (D : Digraph V) (color : V → V → Fin 3)
    (C : Finset V) (s t : V) (i : Fin 3)
    (h : Relation.ReflTransGen
      (fun x y : V => x ∈ C ∧ y ∈ C ∧ D.Adj x y ∧ color x y = i) s t) :
    Relation.ReflTransGen (fun x y : V => D.Adj x y ∧ color x y = i) s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨hbc.2.2.1, hbc.2.2.2⟩

open OPG1808Sol in
theorem solution
    {V : Type} [Fintype V]
    (D : Digraph V) (color : ArcColoring V)
    (C : Finset V) (s : V)
    (hsC : s ∈ C)
    (hdom : ∀ x ∈ C, ∀ y : V, y ∉ C → D.Adj x y)
    (hsrc : ∀ t ∈ C, ∃ i : Fin 3,
      Relation.ReflTransGen (fun x y : V => x ∈ C ∧ y ∈ C ∧ D.Adj x y ∧ color x y = i) s t) :
    IsMonochromaticSource D color s := by
  intro t
  by_cases ht : t ∈ C
  · obtain ⟨i, hi⟩ := hsrc t ht
    exact ⟨i, opg1808sol_lift_path D color C s t i hi⟩
  · exact ⟨color s t, Relation.ReflTransGen.single ⟨hdom s hsC t ht, rfl⟩⟩

#print axioms solution
