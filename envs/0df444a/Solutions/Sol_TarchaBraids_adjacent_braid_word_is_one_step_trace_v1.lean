-- Prove2me | solution 1 for TarchaBraids.adjacent_braid_word_is_one_step_trace_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T08:22:04.540963+00:00
-- url     : https://prove2.me/submissions/77fa562f-d3a4-421b-9e89-52b1509c0083

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

open BraidsLinksMCG TarchaBraids

theorem solution {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    GeomRelatorTrace n
      (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) := by
  let r : FreeGroup (Fin (n - 1)) :=
    FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹
  have hr : r ∈ braidRels n := by
    simp only [braidRels, Set.mem_setOf_eq, Set.mem_union]
    right
    exact ⟨i, j, hji, rfl⟩
  simpa [r] using
    (GeomRelatorTrace.step (n := n) (w := 1) (u := 1) (r := r)
      (GeomRelatorTrace.nil (n := n)) hr)
