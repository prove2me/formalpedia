-- Prove2me | solution 1 for Replay.maxReplay_unique_config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:04:31.07666+00:00
-- url     : https://prove2.me/submissions/73cae365-acfa-4d99-88de-84d2f3a8c942

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R
namespace Replay
theorem _root_.solution {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMaxReplay F R l σ₁) (h₂ : isMaxReplay F R l σ₂) :
    (conf F σ₁).1 = (conf F σ₂).1 :=
  Set.Subset.antisymm (h₂.2 σ₁ h₁.1) (h₁.2 σ₂ h₂.1)
end Replay
