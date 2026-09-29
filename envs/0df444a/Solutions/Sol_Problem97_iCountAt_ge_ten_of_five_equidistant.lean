-- Prove2me | solution 1 for Problem97.iCountAt_ge_ten_of_five_equidistant
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T03:19:55.994714+00:00
-- url     : https://prove2.me/submissions/9ee505fe-2552-4f96-a9ad-9ba2dcb289fc

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_iCountAt_ge_choose_two_of_equidistant_subset

open scoped EuclideanGeometry
open Problem97

/-!
# Ten local isosceles pairs from five equidistant neighbors

In the Dumitrescu (2006) counting convention, five equidistant neighbors
provide at least `choose(5, 2) = 10` unordered pairs at the apex.

The proof is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem solution
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hScard : 5 ≤ S.card)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    10 ≤ iCountAt A p := by
  calc
    10 = (5 : ℕ).choose 2 := by decide
    _ ≤ S.card.choose 2 := Nat.choose_le_choose 2 hScard
    _ ≤ iCountAt A p :=
      iCountAt_ge_choose_two_of_equidistant_subset A p S hSsub hSdist
