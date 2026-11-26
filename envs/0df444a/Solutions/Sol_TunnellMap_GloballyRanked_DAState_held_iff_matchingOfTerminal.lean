-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.held_iff_matchingOfTerminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:01.970804+00:00
-- url     : https://prove2.me/submissions/c64b333b-c9ad-46b3-a1ea-fa6b86d5f256

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_assigned_matchingOfTerminal

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
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = [])
    (s : S) (t : T) :
    st.held t = some s ↔ matchingOfTerminal I hcard st hv hqueue s = t := by
  constructor
  · intro hheld
    have hassigned := (hv.held_iff_assigned s t).mp hheld
    have hfinal := assigned_matchingOfTerminal I hcard st hv hqueue s
    exact Option.some.inj (hfinal.symm.trans hassigned)
  · intro hmatch
    apply (hv.held_iff_assigned s t).mpr
    rw [← hmatch]
    exact assigned_matchingOfTerminal I hcard st hv hqueue s
end TunnellMap.GloballyRanked.DAState
