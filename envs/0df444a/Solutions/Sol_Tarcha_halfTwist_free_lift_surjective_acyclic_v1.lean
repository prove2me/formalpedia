-- Prove2me | solution 1 for Tarcha.halfTwist_free_lift_surjective_acyclic_v1
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-27T00:44:49.722595+00:00
-- url     : https://prove2.me/submissions/228dbc56-c432-4515-ad37-f251694a08ab

import Mathlib

set_option autoImplicit false

-- Solution for Tarcha.halfTwist_free_lift_surjective_acyclic_v1
-- (0fd0aa4a-efe1-4694-8005-f76cd887f183): the algebraic half of the Tarcha
-- fallback leaf ba75baa2. If every element of G is a finite product of
-- f(i) / f(i)^-1, then FreeGroup.lift f is surjective.

theorem solution {ι : Type} {G : Type} [Group G]
    (f : ι → G)
    (hgen : ∀ g : G, ∃ l : List (ι × Bool),
      g = (l.map fun p => if p.2 then f p.1 else (f p.1)⁻¹).prod) :
    Function.Surjective (FreeGroup.lift f) := by
  intro g
  obtain ⟨l, hl⟩ := hgen g
  refine ⟨(l.map fun p => if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹).prod, ?_⟩
  have hterm : ∀ p : ι × Bool,
      ⇑(FreeGroup.lift f) (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹)
        = if p.2 then f p.1 else (f p.1)⁻¹ := by
    intro p
    split_ifs with h
    · exact FreeGroup.lift_apply_of
    · rw [map_inv, FreeGroup.lift_apply_of]
  have key : ⇑(FreeGroup.lift f)
      ((l.map fun p => if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹).prod) =
      (l.map fun p => if p.2 then f p.1 else (f p.1)⁻¹).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    show ⇑(FreeGroup.lift f) (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹)
      = if p.2 then f p.1 else (f p.1)⁻¹
    exact hterm p
  rw [hl]
  exact key
