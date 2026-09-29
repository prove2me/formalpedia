-- Prove2me | solution 1 for TarchaBraids.strandIdx_swap_free_lift_surjective_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T06:49:25.618166+00:00
-- url     : https://prove2.me/submissions/455f4479-b9c3-4c34-b16d-04ec969a9f09

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_TarchaBraids_adjacent_swap_free_lift_surjective_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) =>
        Equiv.swap (strandIdx i) (strandIdxSucc i))) := by
  rcases n with _ | m
  · intro σ
    exact ⟨1, Subsingleton.elim _ _⟩
  · have hgen :
        (fun i : Fin m =>
          Equiv.swap (strandIdx (n := m + 1) i) (strandIdxSucc (n := m + 1) i))
          =
        (fun i : Fin m =>
          (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (m + 1)))) := by
      funext i
      congr
    simpa [hgen] using
      (TarchaBraids.adjacent_swap_free_lift_surjective_v1 m)
