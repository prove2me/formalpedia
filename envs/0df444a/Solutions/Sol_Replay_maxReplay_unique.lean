-- Prove2me | solution 1 for Replay.maxReplay_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:17:16.5408+00:00
-- url     : https://prove2.me/submissions/79e380c1-365b-4a6e-b8b1-211457a514ae

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay
import Theorems.Thm_Replay_maxReplay_unique_config

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R
namespace Replay
theorem _root_.solution {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMaxReplay F R l σ₁) (h₂ : isMaxReplay F R l σ₂) :
    conf F σ₁ = conf F σ₂ :=
  Subtype.ext (maxReplay_unique_config F R h₁ h₂)
end Replay
