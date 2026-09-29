-- Prove2me | solution 1 for TarchaBraids.far_comm_word_is_one_step_trace_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T09:24:24.954613+00:00
-- url     : https://prove2.me/submissions/8a1683c6-2add-43e1-9d4e-9778246b8db9

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

open BraidsLinksMCG TarchaBraids

theorem solution {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    GeomRelatorTrace n
      (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
        (FreeGroup.of j)⁻¹) := by
  let r : FreeGroup (Fin (n - 1)) :=
    FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
      (FreeGroup.of j)⁻¹
  have hr : r ∈ braidRels n := by
    simp only [braidRels, Set.mem_setOf_eq, Set.mem_union]
    left
    exact ⟨i, j, hij, rfl⟩
  simpa [r] using
    (GeomRelatorTrace.step (n := n) (w := 1) (u := 1) (r := r)
      (GeomRelatorTrace.nil (n := n)) hr)
