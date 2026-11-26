-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.matchingOfTerminal_symm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:35:00.499035+00:00
-- url     : https://prove2.me/submissions/ea221f4f-1b30-4f0c-87ff-610aec6563e8

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_held_iff_matchingOfTerminal
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList


attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply

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
    (s : S) (t : T) (hheld : st.held t = some s) :
    (matchingOfTerminal I hcard st hv hqueue).symm t = s := by
  rw [← (matchingOfTerminal I hcard st hv hqueue).injective.eq_iff]
  simp only [Equiv.apply_symm_apply]
  exact ((held_iff_matchingOfTerminal I hcard st hv hqueue s t).mp hheld).symm
end TunnellMap.GloballyRanked.DAState
