-- Prove2me | solution 1 for Stable.subset_replaySet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:17:54.891516+00:00
-- url     : https://prove2.me/submissions/9af64c62-edb1-49a1-beb5-07440f37ac05

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Theorems.Thm_Stable_hist_mem


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
omit hc hlc
namespace Stable
theorem _root_.solution : l ⊆ replaySet F c l :=
  fun _ hx => Set.mem_biUnion hx hist_mem
end Stable
