-- Prove2me | solution 1 for Replay.downset_isConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:07:30.413135+00:00
-- url     : https://prove2.me/submissions/c778bb95-25d5-4da3-8bf2-a34827a41847

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Prime_Log
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Definitions.Def_EventStructures_Prime_Replay
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_ConfFamily_TraceEquivFrom_symm


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
theorem _root_.solution (e : es.Event) : isConf es (downset es e) :=
  ⟨fun h₁ h₂ hc => es.conflict_irrefl e
     (es.conflict_hereditary (es.conflict_symm.symm _ _ (es.conflict_hereditary hc h₂)) h₁),
   fun hx hle => le_trans hle hx⟩
end Replay
