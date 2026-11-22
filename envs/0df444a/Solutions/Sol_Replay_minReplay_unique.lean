-- Prove2me | solution 1 for Replay.minReplay_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:17:06.219886+00:00
-- url     : https://prove2.me/submissions/4edfe10f-9ea7-430b-90a0-d02082eea2c2

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay
import Theorems.Thm_Replay_minReplay_unique_config

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R
namespace Replay
theorem _root_.solution {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMinReplay F R l σ₁) (h₂ : isMinReplay F R l σ₂) :
    conf F σ₁ = conf F σ₂ :=
  Subtype.ext (minReplay_unique_config F R h₁ h₂)
end Replay
