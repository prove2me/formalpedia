-- Prove2me | solution 1 for TunnellMap.GloballyRanked.deferredAcceptance_output_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:31.950126+00:00
-- url     : https://prove2.me/submissions/fd524388-2fef-4e44-9fb1-7b6538b6051f

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_stable_of_deferredAcceptanceCertificate
import Theorems.Thm_TunnellMap_GloballyRanked_exists_unique_stable


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (hcard : Fintype.card S = Fintype.card T)
    (M : S ≃ T) (hM : I.DeferredAcceptanceCertificate M) :
    M = Classical.choose (I.exists_unique_stable hcard) := by
  classical
  exact (Classical.choose_spec (I.exists_unique_stable hcard)).2 M
    (I.stable_of_deferredAcceptanceCertificate M hM)
end TunnellMap.GloballyRanked
