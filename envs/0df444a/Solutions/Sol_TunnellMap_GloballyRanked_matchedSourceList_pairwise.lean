-- Prove2me | solution 1 for TunnellMap.GloballyRanked.matchedSourceList_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:42:46.268111+00:00
-- url     : https://prove2.me/submissions/f1293b7b-ba4f-4d8e-b64c-eff98dfb5495

import Definitions.Def_TunnellMap_ParkingTotal
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_TunnellMap_MatchedOrder
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedSourceList M).Pairwise fun s₁ s₂ =>
      I.rank s₁ (M s₁) ≤ I.rank s₂ (M s₂) := by
  classical
  let r : S → S → Prop := fun s₁ s₂ =>
    I.rank s₁ (M s₁) ≤ I.rank s₂ (M s₂)
  letI : Std.Total r := ⟨fun s₁ s₂ => le_total _ _⟩
  letI : IsTrans S r := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
  simpa [matchedSourceList, r] using
    (List.pairwise_mergeSort' r (Finset.univ : Finset S).toList)
end TunnellMap.GloballyRanked
