-- Prove2me | solution 1 for TunnellMap.GloballyRanked.matchedKeyOrderEquiv_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:43:32.60338+00:00
-- url     : https://prove2.me/submissions/4d6d9df9-1c92-4621-ae12-ec7b3fa7fbb2

import Definitions.Def_TunnellMap_ParkingTotal
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_TunnellMap_MatchedOrder
import Theorems.Thm_TunnellMap_GloballyRanked_matchedSourceList_pairwise
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
    I.MatchedKeyOrder M (I.matchedKeyOrderEquiv M) := by
  classical
  intro i j hkey
  let l := I.matchedSourceList M
  let cast : Fin (Fintype.card S) ≃ Fin l.length :=
    finCongr (I.length_matchedSourceList M).symm
  have horderApply (k : Fin (Fintype.card S)) :
      I.matchedKeyOrderEquiv M k = l.get (cast k) := rfl
  by_contra hij
  have hji : j ≤ i := le_of_not_gt hij
  rcases hji.eq_or_lt with hEq | hlt
  · subst j
    exact (lt_irrefl _ hkey)
  · have hcast : cast j < cast i := by
      simpa [cast] using hlt
    have hle := (I.matchedSourceList_pairwise M).rel_get_of_lt hcast
    rw [horderApply, horderApply] at hkey
    exact (not_lt_of_ge hle) hkey
end TunnellMap.GloballyRanked
