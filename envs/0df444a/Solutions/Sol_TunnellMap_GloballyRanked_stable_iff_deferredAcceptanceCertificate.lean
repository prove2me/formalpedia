-- Prove2me | solution 1 for TunnellMap.GloballyRanked.stable_iff_deferredAcceptanceCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:21.892245+00:00
-- url     : https://prove2.me/submissions/bf3fded9-9e13-4f00-80d7-a2923fb9960d

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_stable_deferredAcceptanceCertificate
import Theorems.Thm_TunnellMap_GloballyRanked_stable_of_deferredAcceptanceCertificate

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) :
    I.Stable M ↔ I.DeferredAcceptanceCertificate M :=
  ⟨I.stable_deferredAcceptanceCertificate M,
    I.stable_of_deferredAcceptanceCertificate M⟩
end TunnellMap.GloballyRanked
