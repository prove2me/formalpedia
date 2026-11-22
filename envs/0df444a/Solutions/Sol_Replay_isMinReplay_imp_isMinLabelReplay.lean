-- Prove2me | solution 1 for Replay.isMinReplay_imp_isMinLabelReplay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:17:26.99639+00:00
-- url     : https://prove2.me/submissions/05308361-357a-4bec-9b6c-1595041f522b

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R
namespace Replay
theorem _root_.solution {l : Set F.Event} {σ : Computations F}
    (h : isMinReplay F R l σ) : isMinLabelReplay F R l σ :=
  ⟨h.1, fun σ' hσ' => Set.image_mono (h.2 σ' hσ')⟩
end Replay
