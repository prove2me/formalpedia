-- Prove2me | solution 1 for TunnellMap.GloballyRanked.preferredTargets_card_eq_preferenceIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:42:18.651672+00:00
-- url     : https://prove2.me/submissions/37943f54-e389-416a-b691-902c8e052721

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
import Theorems.Thm_TunnellMap_GloballyRanked_get_preferenceIndex
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceIndex_injective
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceIndex_lt_iff_rank_lt
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_nodup
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_strict
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList


attribute [local simp] TunnellMap.GloballyRanked.get_preferenceIndex

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution
    (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    (I.preferredTargets M s).card = (I.preferenceIndex s (M s)).1 := by
  let i := I.preferenceIndex s (M s)
  let f : {t // t ∈ I.preferredTargets M s} → Fin i.1 := fun t =>
    ⟨(I.preferenceIndex s t.1).1, by
      have hrank : I.rank s t.1 < I.rank s (M s) := by
        simpa [preferredTargets] using (Finset.mem_filter.mp t.2).2
      exact (I.preferenceIndex_lt_iff_rank_lt s t.1 (M s)).2 hrank⟩
  have hf : Function.Injective f := by
    intro t₁ t₂ h
    have hval : (I.preferenceIndex s t₁.1).1 =
        (I.preferenceIndex s t₂.1).1 := by
      simpa [f] using congrArg Fin.val h
    apply Subtype.ext
    apply I.preferenceIndex_injective s
    apply Fin.ext
    exact hval
  let g : Fin i.1 → {t // t ∈ I.preferredTargets M s} := fun j =>
    ⟨(I.preferenceList s).get
        ⟨j.1, lt_trans j.2 i.2⟩, by
      simp only [preferredTargets, Finset.mem_filter, Finset.mem_univ, true_and]
      have hstrict := I.preferenceList_strict s
        (i := ⟨j.1, lt_trans j.2 i.2⟩) (j := i) j.2
      rw [I.get_preferenceIndex s (M s)] at hstrict
      exact hstrict⟩
  have hg : Function.Injective g := by
    intro j₁ j₂ h
    have hind := (I.preferenceList_nodup s).injective_get
      (congrArg Subtype.val h)
    apply Fin.ext
    exact congrArg
      (fun k : Fin (I.preferenceList s).length => k.1) hind
  have hle : (I.preferredTargets M s).card ≤ i.1 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  have hge : i.1 ≤ (I.preferredTargets M s).card := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective g hg
  exact Nat.le_antisymm hle hge
end TunnellMap.GloballyRanked
