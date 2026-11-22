-- Prove2me | solution 1 for Replay.minReplay_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:55.808337+00:00
-- url     : https://prove2.me/submissions/c1018315-4116-48ab-83ef-0952df71e115

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
import Theorems.Thm_Replay_minReplaySet_is_minimal_replay

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
theorem _root_.solution (l : Set es.Event)
    (hexists : ∃ σ : Computations es.toFamily,
      (Replay.conf es.toFamily σ).1 = minReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es.toFamily, Replay.isMinReplay es.toFamily es.conflict l σ := by
  obtain ⟨σ, h_conf, h_compat⟩ := hexists
  exact ⟨σ, minReplaySet_is_minimal_replay es h_conf h_compat⟩
end Replay
