-- Prove2me | solution 1 for Replay.downset_compatible_with_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:07:21.809577+00:00
-- url     : https://prove2.me/submissions/34c00c23-11c5-4ac5-9a34-1cdc78270b8f

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
theorem _root_.solution {l : Set es.Event} {e x : es.Event}
    (he : e ∈ l) (hxe : x ≤ e)
    (hl_conflict_free : ∀ {e₁ e₂}, e₁ ∈ l → e₂ ∈ l → ¬(e₁ # e₂)) :
    ∀ e' ∈ l, ¬(x # e') := by
  intro e' he' hconf
  have hconf_symm := es.conflict_symm.symm _ _ hconf
  have : e' # e := es.conflict_hereditary hconf_symm hxe
  have : e # e' := es.conflict_symm.symm _ _ this
  exact hl_conflict_free he he' this
end Replay
