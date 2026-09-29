-- Prove2me | solution 1 for Problem97.iCountAt_ge_choose_two_of_equidistant_subset
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T03:18:33.246132+00:00
-- url     : https://prove2.me/submissions/f243d22f-78fc-486f-9b86-a12259bf7fee

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Mathlib.Data.Finset.Powerset

open scoped EuclideanGeometry
open Problem97
open Finset Classical

/-!
# Local isosceles count from an equidistant subset

In the Dumitrescu (2006) counting convention, every unordered pair in an
equidistant set of neighbors contributes one local isosceles pair. The proof
keeps the representation-level powerset containment lemma private and exposes
only the mathematical lower bound.

The proof is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
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
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    S.card.choose 2 ≤ iCountAt A p := by
  calc
    S.card.choose 2 = (S.powersetCard 2).card := (S.card_powersetCard 2).symm
    _ ≤ iCountAt A p :=
      card_le_card (powersetCard_two_subset_isoscelesPairsAt_of_equidistant_subset
        A p S hSsub hSdist)
