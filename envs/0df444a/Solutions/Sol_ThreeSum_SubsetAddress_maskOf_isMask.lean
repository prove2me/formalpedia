-- Prove2me | solution 1 for ThreeSum.SubsetAddress.maskOf_isMask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:30.120738+00:00
-- url     : https://prove2.me/submissions/76168564-261a-493d-9a30-0aa323545be6

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_succ_low
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_succ_high
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
namespace ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range (L + 1)) (hL : L ∉ s) : s ⊆ Finset.range L := by
  intro i hi
  have hb := Finset.mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact Finset.mem_range.mpr (by omega)
end ThreeSum.SubsetAddress
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range L) :
    IsMask L s.card (maskOf s) := by
  induction L generalizing s with
  | zero =>
      have he : s = ∅ := by simpa using hs
      subst s
      simp [maskOf]
  | succ L ih =>
      by_cases hL : L ∈ s
      · have ht : s.erase L ⊆ Finset.range L :=
          subset_range_pred ((Finset.erase_subset L s).trans hs) (Finset.notMem_erase _ _)
        have hm := (ih ht).succ_high
        have hcard : (s.erase L).card + 1 = s.card := Finset.card_erase_add_one hL
        have he : 2 ^ L + maskOf (s.erase L) = maskOf s :=
          Finset.add_sum_erase s (fun i => 2 ^ i) hL
        simpa only [hcard, he] using hm
      · exact (ih (subset_range_pred hs hL)).succ_low
end ThreeSum.SubsetAddress
