-- Prove2me | solution 1 for Replay.downset_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:42.478806+00:00
-- url     : https://prove2.me/submissions/1bbc4683-5913-4b8b-aca7-083f5685caa9

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
theorem _root_.solution {e x y : es.Event} (hxy : x ≤ y) (hy : y ∈ downset es e) :
    x ∈ downset es e :=
  le_trans hxy hy
end Replay
