-- Prove2me | solution 1 for Problem97.six_mul_card_le_iCount_of_K4
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T01:02:52.53723+00:00
-- url     : https://prove2.me/submissions/aaec9d6b-90fc-40d1-9ba4-8d08f0b6940a

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna <adam@mysticflounder.ai>
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_iCountAt_ge_six_of_K4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped EuclideanGeometry
open Problem97
open Finset Classical

/-!
# Total isosceles count lower bound under the four-equidistant property

This is the Dumitrescu (2006) counting step: the six isosceles pairs forced
at each vertex are summed over the finite point set. Equilateral triangles
use the convention that counts them three times.

The proof is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.
-/

theorem solution {A : Finset ℝ²}
    (hK4 : HasNEquidistantProperty 4 A) : 6 * A.card ≤ iCount A := by
  classical
  unfold iCount
  have hpoint : ∀ p ∈ A, 6 ≤ iCountAt A p :=
    fun p hp => iCountAt_ge_six_of_K4 A p (hK4 p hp)
  calc 6 * A.card
      = ∑ _p ∈ A, 6 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ A, iCountAt A p := sum_le_sum hpoint
