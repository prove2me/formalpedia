-- Prove2me | solution 1 for TunnellMap.GloballyRanked.stable_to_partialStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:18:53.564707+00:00
-- url     : https://prove2.me/submissions/be18fa93-e8b6-4eaf-be39-99265a5c75ca

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [LT K] (I : GloballyRanked K S T) (M : S ≃ T)
    (hM : I.Stable M) : I.PartialStable M.toPartialEquiv := by
  intro s t hblock
  apply hM s t
  simpa [PartialBlocks, Blocks] using hblock
end TunnellMap.GloballyRanked
