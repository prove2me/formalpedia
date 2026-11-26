-- Prove2me | solution 1 for TunnellMap.GloballyRanked.earlierMatchedSources_card_le_position
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:00.866883+00:00
-- url     : https://prove2.me/submissions/44396281-2069-454d-9d93-fd5f975915a7

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [Fintype T] [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (order : Fin (Fintype.card S) ≃ S)
    (horder : I.MatchedKeyOrder M order) (i : Fin (Fintype.card S)) :
    (I.earlierMatchedSources M (order i)).card ≤ i.1 := by
  let f : {s' // s' ∈ I.earlierMatchedSources M (order i)} → Fin i.1 :=
    fun s' => ⟨(order.symm s'.1).1, by
      apply horder (order.symm s'.1) i
      have hkey := (Finset.mem_filter.mp s'.2).2
      simpa only [Equiv.apply_symm_apply] using hkey⟩
  have hf : Function.Injective f := by
    intro s₁ s₂ h
    apply Subtype.ext
    apply order.symm.injective
    apply Fin.ext
    simpa [f] using congrArg Fin.val h
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf
end TunnellMap.GloballyRanked
