-- Prove2me | solution 1 for TunnellMap.GloballyRanked.stable_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:03.209397+00:00
-- url     : https://prove2.me/submissions/df0f7218-fb36-483f-bc2e-2173fbb1f2fd

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Theorems.Thm_TunnellMap_GloballyRanked_stable_exists_bounded

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T) :
    ∃ M : S ≃ T, I.Stable M :=
  stable_exists_bounded I hcard (Fintype.card S) le_rfl
end TunnellMap.GloballyRanked
