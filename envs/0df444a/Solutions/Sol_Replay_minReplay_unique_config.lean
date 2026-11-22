-- Prove2me | solution 1 for Replay.minReplay_unique_config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:04:07.00335+00:00
-- url     : https://prove2.me/submissions/972e7ab5-4f70-4404-af61-cac84993361b

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R
namespace Replay
theorem _root_.solution {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMinReplay F R l σ₁) (h₂ : isMinReplay F R l σ₂) :
    (conf F σ₁).1 = (conf F σ₂).1 :=
  Set.Subset.antisymm (h₁.2 σ₂ h₂.1) (h₂.2 σ₁ h₁.1)
end Replay
