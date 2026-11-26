-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.mem_take_of_rank_lt_of_mem_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:35:07.972287+00:00
-- url     : https://prove2.me/submissions/cd0fe277-e167-446c-893c-dbb61cd7c9d5

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_strict
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (s : S) {t u : T} {k : ℕ}
    (hrank : I.rank s t < I.rank s u)
    (hu : u ∈ (I.preferenceList s).take k) :
    t ∈ (I.preferenceList s).take k := by
  let l := I.preferenceList s
  obtain ⟨j, hjMin, hjEq⟩ := List.mem_take_iff_getElem.mp hu
  have htMem : t ∈ l := I.mem_preferenceList s t
  obtain ⟨i, hiLen, hiEq⟩ := List.mem_iff_getElem.mp htMem
  have hjLen : j < l.length := lt_of_lt_of_le hjMin (Nat.min_le_right _ _)
  have hij : i < j := by
    by_contra hnot
    have hji : j ≤ i := Nat.le_of_not_gt hnot
    rcases hji.eq_or_lt with hEq | hlt
    · subst i
      have htu : t = u := hiEq.symm.trans hjEq
      exact (ne_of_lt hrank) (congrArg (I.rank s) htu)
    · have hstrict := I.preferenceList_strict s
          (i := ⟨j, hjLen⟩) (j := ⟨i, hiLen⟩) hlt
      have hgetJ : l.get ⟨j, hjLen⟩ = u := hjEq
      have hgetI : l.get ⟨i, hiLen⟩ = t := hiEq
      rw [hgetJ, hgetI] at hstrict
      exact (not_lt_of_ge hrank.le) hstrict
  apply List.mem_take_iff_getElem.mpr
  refine ⟨i, ?_, hiEq⟩
  exact lt_min (hij.trans (lt_of_lt_of_le hjMin (Nat.min_le_left _ _))) hiLen
end TunnellMap.GloballyRanked.DAState
