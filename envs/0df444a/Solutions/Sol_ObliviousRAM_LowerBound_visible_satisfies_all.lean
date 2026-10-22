-- Prove2me | solution 1 for ObliviousRAM.LowerBound.visible_satisfies_all
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:25:49.618354+00:00
-- url     : https://prove2.me/submissions/21155b77-d756-4da5-93a8-9898476bac79

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

set_option autoImplicit false
open ObliviousRAM.LowerBound

theorem solution {b m t : ℕ} (P : ObliviousPlayer b m t)
    (r : Fin t → Fin m) (a : List (Action m)) (ha : a ∈ (P.play r).support)
    (r' : Fin t → Fin m) :
    ∃ a' ∈ (P.play r').support, visible a' = visible a ∧ Satisfies b a' r' := by
  have h1 : visible a ∈ ((P.play r).map visible).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨a, ha, rfl⟩
  rw [P.oblivious r r'] at h1
  obtain ⟨a', ha', hv⟩ := (PMF.mem_support_map_iff _ _ _).1 h1
  exact ⟨a', ha', hv, P.correct r' a' ha'⟩
