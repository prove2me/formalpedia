-- Prove2me | solution 1 for Replay.minReplaySet_subset_maxReplaySet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:53.250633+00:00
-- url     : https://prove2.me/submissions/25a3b583-a4db-44e2-a337-54ec306fd0ba

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
theorem _root_.solution {l : Set es.Event} :
    minReplaySet es l ⊆ maxReplaySet es l :=
  Set.subset_union_left
end Replay
