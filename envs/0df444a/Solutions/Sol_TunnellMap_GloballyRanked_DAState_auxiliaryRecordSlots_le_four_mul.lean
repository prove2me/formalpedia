-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.auxiliaryRecordSlots_le_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:35:27.728151+00:00
-- url     : https://prove2.me/submissions/d077682b-fa18-45f0-85b0-a35c4b8f0840

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    st.auxiliaryRecordSlots I ≤ 4 * Fintype.card S := by
  have hqueue : st.queue.length ≤ Fintype.card S :=
    hv.queue_nodup.length_le_card
  unfold auxiliaryRecordSlots
  omega
end TunnellMap.GloballyRanked.DAState
