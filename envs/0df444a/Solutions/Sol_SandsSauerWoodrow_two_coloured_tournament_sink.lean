-- Prove2me | solution 1 for SandsSauerWoodrow.two_coloured_tournament_sink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-17T05:08:18.492755+00:00
-- url     : https://prove2.me/submissions/d7c30f9d-9f6c-47c1-be5e-f8322572009d

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_MonoIndependent
import Theorems.Thm_SandsSauerWoodrow_two_coloured_digraph

open OPG1808
open SandsSauerWoodrow

universe u

/-- A single arc is a monochromatic path. -/
private lemma reach_of_arc {V : Type u} {D : Digraph V} {color : ArcColoring V} {a b : V}
    (h : D a b) : MonochromaticallyReaches D color a b :=
  ⟨color a b, Relation.ReflTransGen.single ⟨h, rfl⟩⟩

/-- On a finite vertex type the hypothesis of Theorem 1 is vacuous: an injective
sequence of vertices cannot exist in a finite type. -/
private lemma no_infinite_outward_of_fintype {V : Type u} [Fintype V] (D : Digraph V)
    (color : ArcColoring V) : NoMonoInfiniteOutwardPath D color := by
  rintro ⟨x, _k, hx, _⟩
  have hinj : Function.Injective (fun i : Fin (Fintype.card V + 1) => x (i : ℕ)) :=
    fun a b h => Fin.ext (hx h)
  have hle := Fintype.card_le_of_injective (fun i : Fin (Fintype.card V + 1) => x (i : ℕ)) hinj
  exact Nat.not_succ_le_self (Fintype.card V) (by simpa using hle)

/-- The two-coloured tournament theorem (Sands-Sauer-Woodrow 1982, Corollary 2),
reduced to the two-coloured digraph theorem (their Theorem 1). On a finite tournament
no monochromatic infinite outward path exists, so Theorem 1 applies and produces a
monochromatically independent set `S`. In a tournament any two distinct vertices are
joined by an arc, and an arc is a monochromatic path, so no two distinct vertices can
both lie in `S`: it is a singleton `{v}`, and every other vertex reaches `v`. -/
theorem solution {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V) (htournament : IsTournament D)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∃ v : V, ∀ x : V, x ≠ v → MonochromaticallyReaches D color x v := by
  obtain ⟨S, hSind, hSreach⟩ :=
    two_coloured_digraph D color htwo (no_infinite_outward_of_fintype D color)
  have hSne : S.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    by_contra h
    have hx : x ∉ S := fun hxs => h ⟨x, hxs⟩
    obtain ⟨s, hs, _⟩ := hSreach x hx
    exact h ⟨s, hs⟩
  obtain ⟨v, hv⟩ := hSne
  refine ⟨v, fun x hxv => ?_⟩
  by_cases hxS : x ∈ S
  · exfalso
    rcases hSind x hxS v hv hxv with ⟨h1, h2⟩
    rcases (htournament.2 hxv).1 with h | h
    · exact h1 (reach_of_arc h)
    · exact h2 (reach_of_arc h)
  · obtain ⟨s, hs, hreach⟩ := hSreach x hxS
    have hsv : s = v := by
      by_contra hsv
      rcases hSind s hs v hv hsv with ⟨h1, h2⟩
      rcases (htournament.2 hsv).1 with h | h
      · exact h1 (reach_of_arc h)
      · exact h2 (reach_of_arc h)
    simpa [hsv] using hreach
