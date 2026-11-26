-- Prove2me | solution 1 for TunnellMap.GloballyRanked.stable_of_deferredAcceptanceCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:21.284363+00:00
-- url     : https://prove2.me/submissions/5dec4767-e698-49fe-952a-7309d42c797b

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.DeferredAcceptanceCertificate M) : I.Stable M := by
  intro s t hblock
  have hfinal := hM s t hblock.1
  exact (not_lt_of_ge hfinal.le) hblock.2
end TunnellMap.GloballyRanked
