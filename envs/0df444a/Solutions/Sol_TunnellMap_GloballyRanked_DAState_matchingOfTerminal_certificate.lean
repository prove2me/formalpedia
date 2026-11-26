-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.matchingOfTerminal_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:10.275786+00:00
-- url     : https://prove2.me/submissions/261e8e32-83f8-479d-b1f3-198ef4ae0c80

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_mem_take_of_rank_lt_of_mem_take
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_assigned_matchingOfTerminal
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_held_iff_matchingOfTerminal
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_symm_eq
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList



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
    (st : I.DAState) (hv : st.Valid I) (hp : st.ProposalValid I)
    (hqueue : st.queue = []) :
    I.DeferredAcceptanceCertificate
      (matchingOfTerminal I hcard st hv hqueue) := by
  let M := matchingOfTerminal I hcard st hv hqueue
  intro s t hsource
  have hfinalAssigned : st.assigned s = some (M s) :=
    assigned_matchingOfTerminal I hcard st hv hqueue s
  have hfinalTried := hp.assigned_tried s (M s) hfinalAssigned
  have htTried := mem_take_of_rank_lt_of_mem_take I s hsource hfinalTried
  obtain ⟨holder, hheld, hle⟩ := hp.held_dominates s t htTried
  have hholder : M.symm t = holder :=
    matchingOfTerminal_symm_eq I hcard st hv hqueue holder t hheld
  rw [hholder]
  apply lt_of_le_of_ne hle
  intro heq
  have hholderEq : holder = s := I.target_injective t heq
  have hmatched : M s = t := by
    apply (held_iff_matchingOfTerminal I hcard st hv hqueue s t).mp
    simpa [hholderEq] using hheld
  rw [hmatched] at hsource
  exact (lt_irrefl _ hsource).elim
end TunnellMap.GloballyRanked.DAState
