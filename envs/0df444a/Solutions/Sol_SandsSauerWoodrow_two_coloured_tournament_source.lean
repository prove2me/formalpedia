-- Prove2me | solution 1 for SandsSauerWoodrow.two_coloured_tournament_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T13:31:30.561063+00:00
-- url     : https://prove2.me/submissions/65ce714f-0f65-45ed-a621-1491fe0b3267

import Definitions.Def_opg1808_colored_tournaments
import Theorems.Thm_SandsSauerWoodrow_two_coloured_tournament_sink

open OPG1808
open SandsSauerWoodrow

universe u

/-- Reversing a reflexive-transitive closure reverses the relation. -/
private lemma rtg_swap {α : Type*} {r : α → α → Prop} {x y : α}
    (h : Relation.ReflTransGen (fun a b => r b a) x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc ih

/-- A monochromatic path in the reversed digraph is a monochromatic path backwards. -/
private lemma reaches_swap {V : Type u} {D : Digraph V} {color : ArcColoring V} {x y : V}
    (h : MonochromaticallyReaches (fun a b : V => D b a) (fun a b : V => color b a) x y) :
    MonochromaticallyReaches D color y x := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, rtg_swap hk⟩

/-- Reversing every arc of a tournament gives a tournament. -/
private lemma isTournament_swap {V : Type u} {D : Digraph V} (h : IsTournament D) :
    IsTournament (fun a b : V => D b a) := by
  refine ⟨fun v => h.1 v, fun u v huv => ?_⟩
  exact ⟨(h.2 huv).1.symm, fun hc => (h.2 huv).2 ⟨hc.2, hc.1⟩⟩

/-- The two-coloured tournament theorem in the source orientation: it follows from the
sink form applied to the tournament with every arc reversed, since reversing a directed
path gives a directed path and preserves monochromaticity. -/
theorem solution {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V) (htournament : IsTournament D)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∃ s : V, IsMonochromaticSource D color s := by
  have htwo' : ∀ u v : V, (fun a b : V => D b a) u v →
      ((fun a b : V => color b a) u v = 0 ∨ (fun a b : V => color b a) u v = 1) :=
    fun u v huv => htwo v u huv
  obtain ⟨v, hv⟩ := two_coloured_tournament_sink (fun a b : V => D b a)
    (fun a b : V => color b a) (isTournament_swap htournament) htwo'
  refine ⟨v, fun t => ?_⟩
  by_cases htv : t = v
  · subst htv
    exact ⟨0, Relation.ReflTransGen.refl⟩
  · exact reaches_swap (hv t htv)
