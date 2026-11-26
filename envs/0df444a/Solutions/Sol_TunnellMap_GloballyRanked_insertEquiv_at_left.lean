-- Prove2me | solution 1 for TunnellMap.GloballyRanked.insertEquiv_at_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:53.140706+00:00
-- url     : https://prove2.me/submissions/82782546-b068-4abe-b041-701114339d48

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [DecidableEq S] [DecidableEq T]
    (s₀ : S) (t₀ : T) (M' : {s // s ≠ s₀} ≃ {t // t ≠ t₀}) :
    insertEquiv s₀ t₀ M' s₀ = t₀ := by
  simp [insertEquiv]
end TunnellMap.GloballyRanked
