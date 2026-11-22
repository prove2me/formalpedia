-- Prove2me | solution 1 for Replay.minReplaySet_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:22:14.21149+00:00
-- url     : https://prove2.me/submissions/90537a34-1665-4ca9-b278-c78c2ecfd3dd

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_SES_toFamily_Config
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] SES.toFamily_Config



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
theorem _root_.solution {l : Set es.Event} {x y : es.Event}
    (hy : y ≤ x) (hx : x ∈ minReplaySet es l) : y ∈ minReplaySet es l := by
  simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hx ⊢
  obtain ⟨e, he, hxe⟩ := hx
  exact ⟨e, he, le_trans hy hxe⟩
end Replay
