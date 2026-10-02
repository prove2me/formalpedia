-- Prove2me | solution 1 for OPG1808.minimal_counterexample_strongly_connected
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:33:14.350533+00:00
-- url     : https://prove2.me/submissions/c11bc2a2-48aa-4d60-ae35-175b54b26e6e

import Mathlib

set_option autoImplicit false

/-! The target's preamble defines `OPG1808.ArcColoring` and
`OPG1808.HasRainbowDirectedTriangle` inline (no Definitions bundle). A solution may not import
its own target module, and redeclaring the same names would clash with it, so the statement below
is written against local aliases with IDENTICAL bodies under a distinct namespace. They are
definitionally equal to the target's constants.

The target has no tournament hypothesis on `D`. Counterexample: `V = Fin 2`, the single arc
`0 → 1`, constant colour `0`. Two vertices cannot carry a triangle; the only proper nonempty set
with all arcs to its complement pointing outward is `{0}`, which trivially contains a
monochromatic source of itself (reflexivity); yet `{0}` is exactly such a dominating set. -/
namespace OPG1808DpSol

abbrev ArcColoring (V : Type) : Type := V → V → Fin 3

abbrev HasRainbowDirectedTriangle {V : Type} (D : Digraph V) (color : ArcColoring V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ D.Adj a b ∧ D.Adj b c ∧ D.Adj c a ∧
    color a b ≠ color b c ∧ color b c ≠ color c a ∧ color c a ≠ color a b

/-- The one-arc digraph `0 → 1` on `Fin 2`. -/
def cexD : Digraph (Fin 2) where
  Adj x y := x = 0 ∧ y = 1

theorem cex_norainbow : ¬ HasRainbowDirectedTriangle cexD (fun _ _ => (0 : Fin 3)) := by
  rintro ⟨a, b, c, -, -, -, -, -, -, h, -, -⟩
  exact h rfl

theorem cex_hmin : ∀ C : Finset (Fin 2), C.Nonempty → C ≠ Finset.univ →
      (∀ x ∈ C, ∀ y : Fin 2, y ∉ C → cexD.Adj x y) →
      ∃ s ∈ C, ∀ t ∈ C, ∃ i : Fin 3,
        Relation.ReflTransGen
          (fun x y : Fin 2 => x ∈ C ∧ y ∈ C ∧ cexD.Adj x y ∧
            (fun _ _ => (0 : Fin 3)) x y = i) s t := by
  intro C hne hU hdom
  -- some vertex is missing from C
  obtain ⟨y, hy⟩ : ∃ y, y ∉ C := by
    by_contra h
    exact hU (Finset.eq_univ_iff_forall.mpr (fun z => by
      by_contra hz
      exact h ⟨z, hz⟩))
  obtain ⟨x, hx⟩ := hne
  have hxy := hdom x hx y hy
  -- hence C = {x}: every t ∈ C also has an arc to y, so t = 0 = x
  refine ⟨x, hx, fun t ht => ⟨0, ?_⟩⟩
  have ht' := hdom t ht y hy
  have : t = x := by
    simp only [cexD] at hxy ht'
    rw [ht'.1, hxy.1]
  subst this
  exact Relation.ReflTransGen.refl

theorem cex_dom : ∃ C : Finset (Fin 2), C.Nonempty ∧ C ≠ Finset.univ ∧
      ∀ x ∈ C, ∀ y : Fin 2, y ∉ C → cexD.Adj x y := by
  refine ⟨{0}, Finset.singleton_nonempty _, ?_, ?_⟩
  · intro h
    have : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by rw [h]; exact Finset.mem_univ _
    simp at this
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    refine ⟨hx, ?_⟩
    omega

end OPG1808DpSol

open OPG1808DpSol in
theorem solution : ¬ (∀ {V : Type} [Fintype V]
    (D : Digraph V) (color : ArcColoring V),
    ¬ HasRainbowDirectedTriangle D color →
    (∀ C : Finset V, C.Nonempty → C ≠ Finset.univ →
      (∀ x ∈ C, ∀ y : V, y ∉ C → D.Adj x y) →
      ∃ s ∈ C, ∀ t ∈ C, ∃ i : Fin 3,
        Relation.ReflTransGen
          (fun x y : V => x ∈ C ∧ y ∈ C ∧ D.Adj x y ∧ color x y = i) s t) →
    ¬ ∃ C : Finset V, C.Nonempty ∧ C ≠ Finset.univ ∧
      ∀ x ∈ C, ∀ y : V, y ∉ C → D.Adj x y) := by
  intro h
  exact h cexD (fun _ _ => (0 : Fin 3)) cex_norainbow cex_hmin cex_dom
