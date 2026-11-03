-- Prove2me | solution 1 for QuantumMaxCutEnergy.tight_odd_uncross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:08:17.022424+00:00
-- url     : https://prove2.me/submissions/e99e851b-5ba5-4b12-b233-896c294f7081

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Theorems.Thm_QuantumMaxCutEnergy_internalSum_add_le
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- **Odd-set uncrossing.** If two odd sets are both tight for `x` and their intersection is odd, then the
intersection and the union are tight as well. This is the step that turns an arbitrary family of tight odd
sets into a laminar one. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hcon : ∀ S : Finset (Fin n), Odd S.card → internalSum x S ≤ ((S.card : ℝ) - 1) / 2)
    (A B : Finset (Fin n)) (hAodd : Odd A.card) (hBodd : Odd B.card)
    (hAiB : Odd (A ∩ B).card)
    (hA : internalSum x A = ((A.card : ℝ) - 1) / 2)
    (hB : internalSum x B = ((B.card : ℝ) - 1) / 2) :
    internalSum x (A ∩ B) = (((A ∩ B).card : ℝ) - 1) / 2 ∧
      internalSum x (A ∪ B) = (((A ∪ B).card : ℝ) - 1) / 2 := by
  classical
  -- the union is odd as well
  have hAuB : Odd (A ∪ B).card := by
    obtain ⟨k, hk⟩ := hAodd
    obtain ⟨l, hl⟩ := hBodd
    obtain ⟨m, hm⟩ := hAiB
    have hle : (A ∩ B).card ≤ A.card := Finset.card_le_card (Finset.inter_subset_left)
    have hcard := Finset.card_union_add_card_inter A B
    refine ⟨k + l - m, ?_⟩
    omega
  -- the two bounds at the union and the intersection
  have h1 := hcon (A ∩ B) hAiB
  have h2 := hcon (A ∪ B) hAuB
  have h3 := internalSum_add_le x hx A B
  have hcard := Finset.card_union_add_card_inter A B
  -- the left side equals the sum of the two bounds
  have hleft : internalSum x A + internalSum x B
      = ((↑(A ∪ B).card : ℝ) - 1) / 2 + ((↑(A ∩ B).card : ℝ) - 1) / 2 := by
    rw [hA, hB]
    have : ((A.card : ℝ) - 1) / 2 + ((B.card : ℝ) - 1) / 2
        = ((↑(A ∪ B).card : ℝ) - 1) / 2 + ((↑(A ∩ B).card : ℝ) - 1) / 2 := by
      have hc : (A.card : ℝ) + (B.card : ℝ) = ((A ∪ B).card : ℝ) + ((A ∩ B).card : ℝ) := by
        rw [← Nat.cast_add, ← Nat.cast_add, hcard]
      linarith
    linarith
  constructor
  · have : internalSum x (A ∪ B) + internalSum x (A ∩ B)
        ≤ ((↑(A ∪ B).card : ℝ) - 1) / 2 + ((↑(A ∩ B).card : ℝ) - 1) / 2 := by linarith
    linarith
  · have : internalSum x (A ∪ B) + internalSum x (A ∩ B)
        ≤ ((↑(A ∪ B).card : ℝ) - 1) / 2 + ((↑(A ∩ B).card : ℝ) - 1) / 2 := by linarith
    linarith

#print axioms solution
