-- Prove2me | solution 1 for ThreeSum.MaskDecode.natPositions_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:30.480054+00:00
-- url     : https://prove2.me/submissions/f9f67296-89a1-449a-b5d2-b41fe3631e50

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDecode
namespace ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
private theorem bitIndices_subset {L m : ℕ} (hm : m < 2^L) :
    m.bitIndices.toFinset ⊆ Finset.range L := by
  intro i hi
  have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
  apply Finset.mem_range.mpr
  by_contra hn
  have hh : 2^L ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hn)
  omega
end ThreeSum.MaskDecode
set_option autoImplicit false
open ThreeSum ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskDecode
theorem _root_.solution {L m : ℕ} (hm : m < 2^L) :
    natPositions (decode L m) = m.bitIndices.toFinset := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
    rw [← he]
    exact List.mem_toFinset.mpr (Finset.mem_filter.mp hj).2
  · intro hi
    have hiL := Finset.mem_range.mp (bitIndices_subset hm hi)
    apply Finset.mem_map.mpr
    refine ⟨⟨i, hiL⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact List.mem_toFinset.mp hi
end ThreeSum.MaskDecode
