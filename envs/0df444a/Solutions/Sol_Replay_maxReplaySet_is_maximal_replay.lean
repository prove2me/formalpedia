-- Prove2me | solution 1 for Replay.maxReplaySet_is_maximal_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:08:32.789992+00:00
-- url     : https://prove2.me/submissions/7c643df1-f80d-4a9f-84f8-cdcb09299c03

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
import Theorems.Thm_Replay_minReplaySet_contains_log

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
open Log
local infixl:50 " ⊨ " => PES.compatibleWithLog es
open Replay
local infixl:50 " ## " => es.minimalConflict
local infixl:50 " # " => es.conflict
namespace Replay
theorem _root_.solution {l : Set es.Event} {σ : Computations es.toFamily}
    (h_conf : (Replay.conf es.toFamily σ).1 = maxReplaySet es l)
    (h_compat : σ ⊨ l) :
    Replay.isMaxReplay es.toFamily es.conflict l σ := by
  constructor
  · exact h_compat
  · intro σ' h'_compat
    rw [h_conf]
    intro x hx
    -- hx : x ∈ (Replay.conf es.toFamily σ').1, need to show: x ∈ maxReplaySet es l
    by_cases hconflict : ∃ e', x # e'
    · -- Case 1: x conflicts with something, so by compatibility x ∈ l ⊆ minReplaySet
      obtain ⟨e', hc⟩ := hconflict
      have x_in_l : x ∈ l := h'_compat.2.2 x hx e' hc
      left
      exact minReplaySet_contains_log es x_in_l
    · -- Case 2: x has no conflicts, show it's in the forced set
      right
      intro e₁ e₂ ⟨hmc, hle⟩
      -- e₁ ## e₂ and e₁ ≤ x
      -- Since x ∈ conf(σ') and configurations are downward-closed, e₁ ∈ conf(σ')
      have he₁_in : e₁ ∈ (Replay.conf es.toFamily σ').1 := (Replay.conf es.toFamily σ').2.2 hx hle
      -- From e₁ ## e₂, we have e₁ # e₂ (minimalConflict.1)
      have hconf_e₁_e₂ : e₁ # e₂ := hmc.1
      -- By compatibility of σ': e₁ ∈ conf(σ') and e₁ # e₂ implies e₁ ∈ l
      exact h'_compat.2.2 e₁ he₁_in e₂ hconf_e₁_e₂
end Replay
