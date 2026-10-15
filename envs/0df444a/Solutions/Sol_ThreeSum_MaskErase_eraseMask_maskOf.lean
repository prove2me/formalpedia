-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_maskOf
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:48:40.67604+00:00
-- url     : https://prove2.me/submissions/b89e8d36-8f97-485f-9230-0173c3e93244

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase

open Finset
open scoped BigOperators
open SubsetAddress





















private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range (L+1)) (hL : L ∉ s) : s ⊆ Finset.range L := by
  intro i hi
  have h := Finset.mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact Finset.mem_range.mpr (by omega)

theorem eraseMask_maskOf_sourceProof {L : ℕ} (s : Finset ℕ) (hs : s ⊆ Finset.range L) (a : ℕ) :
    eraseMask L a (maskOf s) = maskOf (s.erase a) := by
  induction L generalizing s with
  | zero =>
    have he : s = ∅ := by simpa using hs
    subst s
    simp [eraseMask, maskOf]
  | succ L ih =>
    by_cases hL : L ∈ s
    · have ht : s.erase L ⊆ Finset.range L :=
        subset_range_pred ((Finset.erase_subset L s).trans hs) (Finset.notMem_erase _ _)
      have he : 2^L + maskOf (s.erase L) = maskOf s :=
        Finset.add_sum_erase s (fun i => 2^i) hL
      have hb := (maskOf_isMask ht).1
      have hlo : ¬maskOf s < 2^L := by omega
      rw [eraseMask, if_neg hlo]
      have hsub : maskOf s - 2^L = maskOf (s.erase L) := by omega
      rw [hsub]
      by_cases ha : a = L
      · simp only [ha, ite_true]
      · rw [if_neg ha, ih (s.erase L) ht]
        have hL' : L ∈ s.erase a := Finset.mem_erase.mpr ⟨Ne.symm ha, hL⟩
        have heer : (s.erase L).erase a = (s.erase a).erase L := by
          ext i
          simp only [Finset.mem_erase]
          tauto
        rw [heer]
        exact Finset.add_sum_erase (s.erase a) (fun i => 2^i) hL'
    · have hs' := subset_range_pred hs hL
      have hlo := (maskOf_isMask hs').1
      rw [eraseMask, if_pos hlo]
      exact ih s hs'

























end ThreeSum.MaskErase

end


theorem solution : ∀ {L : Nat} (s : Finset.{0} Nat),
  @LE.le.{0} (Finset.{0} Nat)
      (@Preorder.toLE.{0} (Finset.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
      s (Finset.range L) →
    ∀ (a : Nat),
      @Eq.{1} Nat (ThreeSum.MaskErase.eraseMask L a (ThreeSum.SubsetAddress.maskOf s))
        (ThreeSum.SubsetAddress.maskOf (@Finset.erase.{0} Nat instDecidableEqNat s a)) := by
  exact @ThreeSum.MaskErase.eraseMask_maskOf_sourceProof

#print axioms solution
