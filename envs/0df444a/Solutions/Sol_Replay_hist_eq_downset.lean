-- Prove2me | solution 1 for Replay.hist_eq_downset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:09:10.47385+00:00
-- url     : https://prove2.me/submissions/f3368963-0e6f-4276-83b7-5eeee0e410dc

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
import Theorems.Thm_Replay_downset_isConf
import Theorems.Thm_Stable_hist_least


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
theorem _root_.solution {c : Set es.Event} (hc : isConf es c) {x : es.Event} (hx : x ∈ c) :
    Stable.hist es.toFamily c x = downset es x :=
  Set.Subset.antisymm
    (Stable.hist_least (F := es.toFamily) (downset_isConf es x) (fun _ hy => hc.2 hx hy) le_rfl)
    (fun _ hy => Set.mem_sInter.mpr (fun _ hm => hm.1.2 hm.2.2 hy))
end Replay
