-- Prove2me | solution 1 for Problem97.fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T02:38:46.789655+00:00
-- url     : https://prove2.me/submissions/25a2d7eb-a0bd-4cbf-a1f9-885160289265

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_six_mul_card_add_one_le_iCount_of_K4_of_iCountAt_ge_seven

section Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount

open scoped EuclideanGeometry
open Problem97

/-!
# Nine-point total isosceles count lower bound from one excess apex

This is the Dumitrescu (2006) counting convention: four equidistant
neighbors at every vertex supply six pairs, and an apex with at least seven
pairs supplies one additional unit. In a nine-point configuration this gives
`55` total isosceles pairs. Equilateral triangles are counted three times.

The proof is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem solution {A : Finset ℝ²} (hcard : A.card = 9)
    (hK4 : HasNEquidistantProperty 4 A) {p : ℝ²} (hpA : p ∈ A)
    (hpExtra : 7 ≤ iCountAt A p) :
    55 ≤ iCount A := by
  have h :=
    six_mul_card_add_one_le_iCount_of_K4_of_iCountAt_ge_seven hK4 hpA hpExtra
  rw [hcard] at h
  norm_num at h
  exact h

end Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount
