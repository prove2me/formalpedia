-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.terminal_cursorTotal_eq_proposalCount_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:46:58.324776+00:00
-- url     : https://prove2.me/submissions/4e668002-4dc8-4c74-93c6-3bbbd3272948

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_terminal_cursor_eq_proposalCount

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
    (st : I.DAState) (hv : st.Valid I) (hlast : st.AssignedLast I)
    (hqueue : st.queue = []) :
    st.cursorTotal I =
      ∑ s : S, I.proposalCount
        (matchingOfTerminal I hcard st hv hqueue) s := by
  unfold cursorTotal
  apply Finset.sum_congr rfl
  intro s _
  exact terminal_cursor_eq_proposalCount I hcard st hv hlast hqueue s
end TunnellMap.GloballyRanked.DAState
