-- Prove2me | solution 1 for Stable.replaySet_least
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:03.317095+00:00
-- url     : https://prove2.me/submissions/7136dd47-8ffa-41fc-af13-2e7265ce20b5

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Theorems.Thm_Stable_hist_least


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
omit hc hlc
namespace Stable
theorem _root_.solution {m : Set F.Event} (hm : F.Config m) (hmc : m ⊆ c) (hlm : l ⊆ m) :
    replaySet F c l ⊆ m := by
  rintro x hx
  obtain ⟨-, ⟨y, rfl⟩, -, ⟨hy, rfl⟩, hxy⟩ := hx
  exact hist_least hm hmc (hlm hy) hxy
end Stable
