-- Prove2me | solution 1 for Replay.replaySet_eq_minReplaySet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:58.002835+00:00
-- url     : https://prove2.me/submissions/d0a59850-11ef-48f8-83df-f280adaea330

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
import Theorems.Thm_Replay_hist_eq_downset

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
theorem _root_.solution {c l : Set es.Event} (hc : isConf es c) (hlc : l ⊆ c) :
    Stable.replaySet es.toFamily c l = minReplaySet es l :=
  Set.iUnion₂_congr (fun _ hy => hist_eq_downset es hc (hlc hy))
end Replay
