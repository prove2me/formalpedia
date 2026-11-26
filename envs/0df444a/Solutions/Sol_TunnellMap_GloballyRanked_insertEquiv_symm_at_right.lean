-- Prove2me | solution 1 for TunnellMap.GloballyRanked.insertEquiv_symm_at_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:03.247804+00:00
-- url     : https://prove2.me/submissions/0845c1fc-31c5-4207-bcb3-c29aa46cb372

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [DecidableEq S] [DecidableEq T]
    (s₀ : S) (t₀ : T) (M' : {s // s ≠ s₀} ≃ {t // t ≠ t₀}) :
    (insertEquiv s₀ t₀ M').symm t₀ = s₀ := by
  simp [insertEquiv]
end TunnellMap.GloballyRanked
