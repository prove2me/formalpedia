-- Prove2me | solution 1 for TunnellMap.GloballyRanked.stable_deferredAcceptanceCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:47.343908+00:00
-- url     : https://prove2.me/submissions/3be94199-55cd-44db-bb9d-5edfbe2e64d3

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) : I.DeferredAcceptanceCertificate M := by
  intro s t hsource
  have htargetLe : I.rank (M.symm t) t ≤ I.rank s t := by
    apply le_of_not_gt
    intro htarget
    exact hM s t ⟨hsource, htarget⟩
  apply lt_of_le_of_ne htargetLe
  intro heq
  have hs : M.symm t = s := I.target_injective t heq
  have ht : t = M s := by
    rw [← hs]
    simp
  rw [ht] at hsource
  exact (lt_irrefl _) hsource
end TunnellMap.GloballyRanked
