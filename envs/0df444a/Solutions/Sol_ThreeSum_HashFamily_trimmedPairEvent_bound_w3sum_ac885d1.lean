-- Prove2me | solution 1 for ThreeSum.HashFamily.trimmedPairEvent_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:10.414807+00:00
-- url     : https://prove2.me/submissions/1e10f59e-cb7b-4a1f-a640-da2f2a1e051b

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card
import Definitions.Def_WeightedCache3SUM_Alias_c1cc563854038150
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool))
    (hL : ∀ u ∈ leftVertices, u ≠ t) (hR : ∀ u ∈ rightVertices, u ≠ s)
    (B : ℕ)
    (hBL : 4 * (Fintype.card K + leftVertices.card) ≤ B * Fintype.card K)
    (hBR : 4 * (Fintype.card K + rightVertices.card) ≤ B * Fintype.card K) :
    Fintype.card (α × Bool → K) ≤ 2 * Fintype.card K ^ 2 *
      (trimmedPairEvent s t a b leftVertices rightVertices B).card := by
  have hsub : pairEvent s t a b ⊆
      (trimmedPairEvent s t a b leftVertices rightVertices B ∪
        heavyPairEvent s t a b leftVertices B) ∪ heavyPairEvent t s b a rightVertices B := by
    intro w hw
    by_cases hl : bucketSize leftVertices w a ≤ B
    · by_cases hr : bucketSize rightVertices w b ≤ B
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hw, hl, hr⟩))
      · have hw' : w ∈ pairEvent t s b a := by simpa [pairEvent, and_comm] using hw
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw', by omega⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hw, by omega⟩))
  have hcard : (pairEvent s t a b).card ≤
      (trimmedPairEvent s t a b leftVertices rightVertices B).card +
        (heavyPairEvent s t a b leftVertices B).card +
          (heavyPairEvent t s b a rightVertices B).card := by
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le ..).trans
      (Nat.add_le_add_right (Finset.card_union_le ..) _))
  have hraw := pairEvent_card hst a b
  have hleft := heavyPairEvent_bound hst a b leftVertices hL B hBL
  have hright := heavyPairEvent_bound (Ne.symm hst) b a rightVertices hR B hBR
  have hscaled := Nat.mul_le_mul_left (4 * Fintype.card K ^ 2) hcard
  nlinarith
end ThreeSum.HashFamily
