-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:11.861799+00:00
-- url     : https://prove2.me/submissions/00c74355-8a59-4ea8-bf73-8d7bd5d38b32

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Definitions.Def_TunnellMap_DeferredAcceptanceOutput

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
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = []) (s : S) :
    matchingOfTerminal I hcard st hv hqueue s =
      assignedTarget I st hv hqueue s := rfl
end TunnellMap.GloballyRanked.DAState
