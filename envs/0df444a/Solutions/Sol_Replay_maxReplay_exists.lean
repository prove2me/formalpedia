-- Prove2me | solution 1 for Replay.maxReplay_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:57.500564+00:00
-- url     : https://prove2.me/submissions/cfb30145-61ec-4b93-9953-b5248f64343a

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
import Theorems.Thm_Replay_maxReplaySet_is_maximal_replay

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
      (Replay.conf es.toFamily σ).1 = maxReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es.toFamily, Replay.isMaxReplay es.toFamily es.conflict l σ := by
  obtain ⟨σ, h_conf, h_compat⟩ := hexists
  exact ⟨σ, maxReplaySet_is_maximal_replay es h_conf h_compat⟩
end Replay
