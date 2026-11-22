-- Prove2me | solution 1 for Stable.replaySet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:17:55.381916+00:00
-- url     : https://prove2.me/submissions/ad191a96-9e0e-4e18-8fad-f67e5a5c8a81

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Theorems.Thm_Stable_hist_subset


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
include hc hlc
namespace Stable
theorem _root_.solution : replaySet F c l ⊆ c := by
  rintro x hx
  obtain ⟨-, ⟨y, rfl⟩, -, ⟨hy, rfl⟩, hxy⟩ := hx
  exact hist_subset hc (hlc hy) hxy
end Stable
