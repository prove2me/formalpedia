-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.queued_cursor_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:10:39.730568+00:00
-- url     : https://prove2.me/submissions/b849c69b-9496-4c0d-b439-ac67f1f53df4

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
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



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (s : S) (hs : s ∈ st.queue) :
    st.cursor s < Fintype.card T := by
  by_contra hnot
  have hcursor : st.cursor s = Fintype.card T := by
    have := st.cursor_le s
    omega
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hs
  have hoccupied : ∀ t : T, st.Occupied I t := by
    intro t
    apply hv.tried_occupied s t
    have ht := I.mem_preferenceList s t
    rw [hcursor, ← I.length_preferenceList s, List.take_length]
    exact ht
  classical
  let holder : T → S := fun t => Classical.choose (hoccupied t)
  have holder_spec (t : T) : st.held t = some (holder t) :=
    Classical.choose_spec (hoccupied t)
  have holder_ne (t : T) : holder t ≠ s := by
    intro heq
    have hassigned := (hv.held_iff_assigned (holder t) t).mp (holder_spec t)
    rw [heq, hsFree] at hassigned
    contradiction
  let f : T → {x : S // x ≠ s} := fun t => ⟨holder t, holder_ne t⟩
  have hf : Function.Injective f := by
    intro t₁ t₂ h
    have hholder : holder t₁ = holder t₂ := congrArg Subtype.val h
    have h₁ := (hv.held_iff_assigned (holder t₁) t₁).mp (holder_spec t₁)
    have h₂ := (hv.held_iff_assigned (holder t₂) t₂).mp (holder_spec t₂)
    rw [hholder] at h₁
    exact Option.some.inj (h₁.symm.trans h₂)
  have hle : Fintype.card T ≤ Fintype.card {x : S // x ≠ s} :=
    Fintype.card_le_of_injective f hf
  have hcompl : Fintype.card {x : S // x ≠ s} = Fintype.card S - 1 := by
    simp
  rw [hcompl, ← hcard] at hle
  have hSpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨s⟩
  have hTpos : 0 < Fintype.card T := by omega
  omega
end TunnellMap.GloballyRanked.DAState
