-- Prove2me | solution 1 for Stable.replaySet_config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:02.845347+00:00
-- url     : https://prove2.me/submissions/d7fea3b1-2df7-4d2e-a6d6-9da7d633407a

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Replay
import Definitions.Def_EventStructures_Stable_Replay
import Theorems.Thm_Stable_hist_config
import Theorems.Thm_Stable_hist_subset


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
variable {c l : Set F.Event} (hc : F.Config c) (hlc : l ⊆ c)
include hc hlc
namespace Stable
theorem _root_.solution (hS : Stable F) (hC : Coherent F) : F.Config (replaySet F c l) := by
  have himg : replaySet F c l = ⋃₀ (hist F c '' l) := by
    rw [Set.sUnion_image]; rfl
  rw [himg]
  exact hC (z := c) (by rintro - ⟨y, hy, rfl⟩; exact hist_config hS hc (hlc hy))
    hc (by rintro - ⟨y, hy, rfl⟩; exact hist_subset hc (hlc hy))
end Stable
