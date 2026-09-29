-- Prove2me | solution 1 for Problem97.fifty_five_le_iCount_of_card_nine_K4_of_five_equidistant
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T03:23:23.270809+00:00
-- url     : https://prove2.me/submissions/debea035-283c-45b5-bd3e-b1f87a8aa146

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_iCountAt_ge_ten_of_five_equidistant
import Theorems.Thm_Problem97_fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven

open scoped EuclideanGeometry
open Problem97

/-!
# Fifty-five total isosceles pairs from the five-equidistant shape

In the Dumitrescu (2006) counting convention, five equidistant neighbors
give at least ten local pairs at one apex. The published excess-apex theorem
then raises the nine-point total to at least `55`.

The proof is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Adrian Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem solution {A : Finset ℝ²}
    (hcard : A.card = 9) (hK4 : HasNEquidistantProperty 4 A)
    {p : ℝ²} (hpA : p ∈ A) {S : Finset ℝ²}
    (hScard : 5 ≤ S.card)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    55 ≤ iCount A := by
  have hlocal : 10 ≤ iCountAt A p :=
    iCountAt_ge_ten_of_five_equidistant A p S hScard hSsub hSdist
  exact fifty_five_le_iCount_of_card_nine_K4_of_iCountAt_ge_seven hcard hK4 hpA
    (le_trans (by decide : 7 ≤ 10) hlocal)
