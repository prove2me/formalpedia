-- Prove2me | solution 1 for Replay.minReplaySet_is_minimal_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:07:24.613878+00:00
-- url     : https://prove2.me/submissions/69231c42-a276-4aeb-aa9c-a2ba5a38f095

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay

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
    (h_conf : (Replay.conf es.toFamily σ).1 = minReplaySet es l)
    (h_compat : σ ⊨ l) :
    Replay.isMinReplay es.toFamily es.conflict l σ := by
  constructor
  · exact h_compat
  · intro σ' h'_compat
    rw [h_conf]
    intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    -- x ≤ e and e ∈ l
    -- σ' ⊨ l means all events in l are in σ'
    have : e ∈ (Replay.conf es.toFamily σ').1 := h'_compat.1 e he
    exact (Replay.conf es.toFamily σ').2.2 this hxe
end Replay
