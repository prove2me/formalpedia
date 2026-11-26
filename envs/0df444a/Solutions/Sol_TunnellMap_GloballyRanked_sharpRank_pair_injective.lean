-- Prove2me | solution 1 for TunnellMap.GloballyRanked.sharpRank_pair_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:23.153165+00:00
-- url     : https://prove2.me/submissions/f2ff3e3a-84a4-4c3d-a9cd-4a43c1905a88

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_matchedProposalCounts
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_matchedProposalCounts



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
namespace TunnellMap.GloballyRanked
theorem _root_.solution (m : ℕ) :
    Function.Injective (fun e : Fin m × Fin m =>
      (sharpRanking m).rank e.1 e.2) := by
  intro e₁ e₂ h
  have htval : e₁.2.1 = e₂.2.1 := by
    have hmod := congrArg (fun k : ℕ => k % (m + 1)) h
    simpa [sharpRanking, sharpRank, Nat.add_mod,
      Nat.mod_eq_of_lt (lt_trans e₁.2.2 (Nat.lt_succ_self m)),
      Nat.mod_eq_of_lt (lt_trans e₂.2.2 (Nat.lt_succ_self m))] using hmod
  have ht : e₁.2 = e₂.2 := Fin.ext htval
  have hsval : e₁.1.1 = e₂.1.1 := by
    change (m + 1) * e₁.1.1 + e₁.2.1 =
      (m + 1) * e₂.1.1 + e₂.2.1 at h
    rw [htval] at h
    apply mul_left_cancel₀ (by omega : m + 1 ≠ 0)
    exact Nat.add_right_cancel h
  exact Prod.ext (Fin.ext hsval) ht
end TunnellMap.GloballyRanked
