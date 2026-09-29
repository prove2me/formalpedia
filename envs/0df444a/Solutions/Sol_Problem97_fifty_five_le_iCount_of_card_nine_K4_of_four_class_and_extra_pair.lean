-- Prove2me | solution 1 for Problem97.fifty_five_le_iCount_of_card_nine_K4_of_four_class_and_extra_pair
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T03:24:56.800143+00:00
-- url     : https://prove2.me/submissions/45dc1c51-cf6d-4a43-99e1-407bec71fef4

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_iCountAt_ge_seven_of_four_class_and_extra_pair
import Theorems.Thm_Problem97_fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven

section Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount

open scoped EuclideanGeometry
open Problem97

/-!
# Nine-point count from a four-class and an extra pair

The local four-class argument supplies seven isosceles pairs at the chosen
apex. The previously published strict nine-point counting theorem then gives
the lower bound `55` for the total count.

The proof is rehosted from `Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem solution
    {A : Finset ℝ²}
    (hcard : A.card = 9) (hK4 : HasNEquidistantProperty 4 A)
    {p u v : ℝ²} (hpA : p ∈ A) {T : Finset ℝ²}
    (hTcard : 4 ≤ T.card)
    (hTsub : T ⊆ A.erase p)
    (hTdist : ∃ r : ℝ, ∀ q ∈ T, dist p q = r)
    (hpair_sub : ({u, v} : Finset ℝ²) ⊆ A.erase p)
    (hpair_card : ({u, v} : Finset ℝ²).card = 2)
    (hpair_dist : ∃ r : ℝ, ∀ q ∈ ({u, v} : Finset ℝ²), dist p q = r)
    (hu_not_mem_T : u ∉ T) :
    55 ≤ iCount A := by
  have hlocal : 7 ≤ iCountAt A p :=
    iCountAt_ge_seven_of_four_class_and_extra_pair A p T u v hTcard hTsub hTdist
      hpair_sub hpair_card hpair_dist hu_not_mem_T
  exact fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven hcard hK4 hpA hlocal

end Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount
