-- Prove2me | solution 2 for SandsSauerWoodrow.leSet_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-17T23:23:48.034989+00:00
-- url     : https://prove2.me/submissions/3a29c315-d440-4eb8-91e0-dcfcdc4521db

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808
open SandsSauerWoodrow

universe u

/-- The order a transitive relation induces on sets is transitive. -/
theorem solution {V : Type u} {R : V → V → Prop} (hR : Transitive R) :
    Transitive (leSet R) := by
  intro S T U hST hTU x hx
  obtain ⟨y, hy, hxy⟩ := hST x hx
  obtain ⟨z, hz, hyz⟩ := hTU y hy
  refine ⟨z, hz, ?_⟩
  rcases hxy with hxy | hxy
  · subst hxy; exact hyz
  · rcases hyz with hyz | hyz
    · subst hyz; exact Or.inr hxy
    · exact Or.inr (hR hxy hyz)
