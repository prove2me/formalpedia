-- Prove2me | solution 1 for Problem97.iCountAt_ge_seven_of_four_class_and_extra_pair
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T03:21:49.835566+00:00
-- url     : https://prove2.me/submissions/866b6ad4-788a-4bb1-b7be-e9f36abdd7f6

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Mathlib.Data.Finset.Powerset

section Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount

open scoped EuclideanGeometry
open Problem97
open Finset Classical

/-!
# Seven local isosceles pairs from a four-class and an extra pair

In the Dumitrescu (2006) counting convention, every unordered pair of points
at a common distance from an apex contributes one local isosceles pair. A
four-point equidistant class contributes six pairs, and the stated extra pair
is distinct from all six because one of its points lies outside the class.

The proof is rehosted from `Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

/-- Every two-point subset of an equidistant set is represented in the local
isosceles-pair finset. -/
private theorem powersetCard_two_subset_isoscelesPairsAt_of_equidistant_subset
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    S.powersetCard 2 ⊆ IsoscelesPairsAt A p := by
  rcases hSdist with ⟨r, hdist⟩
  intro t ht
  rcases mem_powersetCard.mp ht with ⟨htsub, htcard⟩
  refine mem_filter.mpr ⟨?_, ⟨r, ?_⟩⟩
  · exact mem_powersetCard.mpr ⟨htsub.trans hSsub, htcard⟩
  · intro q hqt
    exact hdist q (htsub hqt)

theorem solution
    (A : Finset ℝ²) (p : ℝ²) (T : Finset ℝ²) (u v : ℝ²)
    (hTcard : 4 ≤ T.card)
    (hTsub : T ⊆ A.erase p)
    (hTdist : ∃ r : ℝ, ∀ q ∈ T, dist p q = r)
    (hpair_sub : ({u, v} : Finset ℝ²) ⊆ A.erase p)
    (hpair_card : ({u, v} : Finset ℝ²).card = 2)
    (hpair_dist : ∃ r : ℝ, ∀ q ∈ ({u, v} : Finset ℝ²), dist p q = r)
    (hu_not_mem_T : u ∉ T) :
    7 ≤ iCountAt A p := by
  let pair : Finset ℝ² := {u, v}
  have hTpow_sub : T.powersetCard 2 ⊆ IsoscelesPairsAt A p :=
    powersetCard_two_subset_isoscelesPairsAt_of_equidistant_subset A p T hTsub hTdist
  have hpair_mem_iso : pair ∈ IsoscelesPairsAt A p := by
    refine mem_filter.mpr ⟨?_, hpair_dist⟩
    exact mem_powersetCard.mpr ⟨hpair_sub, hpair_card⟩
  have hpair_not_mem_Tpow : pair ∉ T.powersetCard 2 := by
    intro hmem
    have hsubT : pair ⊆ T := (mem_powersetCard.mp hmem).1
    have hu_pair : u ∈ pair := by simp [pair]
    exact hu_not_mem_T (hsubT hu_pair)
  have hinsert_sub : insert pair (T.powersetCard 2) ⊆ IsoscelesPairsAt A p := by
    intro x hx
    rcases mem_insert.mp hx with hxpair | hxT
    · simpa [hxpair] using hpair_mem_iso
    · exact hTpow_sub hxT
  have hSix : 6 ≤ (T.powersetCard 2).card := by
    calc
      6 = (4 : ℕ).choose 2 := by decide
      _ ≤ T.card.choose 2 := Nat.choose_le_choose 2 hTcard
      _ = (T.powersetCard 2).card := (T.card_powersetCard 2).symm
  have hSeven : 7 ≤ (insert pair (T.powersetCard 2)).card := by
    rw [card_insert_of_notMem hpair_not_mem_Tpow]
    simpa using Nat.add_le_add_right hSix 1
  exact le_trans hSeven (card_le_card hinsert_sub)

end Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount
