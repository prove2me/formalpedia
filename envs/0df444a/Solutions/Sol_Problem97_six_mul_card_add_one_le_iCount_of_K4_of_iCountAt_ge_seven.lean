-- Prove2me | solution 1 for Problem97.six_mul_card_add_one_le_iCount_of_K4_of_iCountAt_ge_seven
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T02:37:23.88181+00:00
-- url     : https://prove2.me/submissions/d049b439-f7fa-454a-98c7-1b604aca3192

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
# Strict total isosceles count lower bound from one excess apex

This is the Dumitrescu (2006) counting convention: four equidistant
neighbors at each vertex supply six pairs, and an apex with at least seven
pairs supplies one additional unit over the baseline. Equilateral triangles
are counted three times.

The proof is rehosted from
`Erdos9796Proof.P97.IsoscelesCount` at source commit
`bd8528ea10a12da2c84a10cc5897e36681c2e75d`.

The counting method is attributed to Dumitrescu (2006); the Lean
formalization is by Adam McKenna.
-/

theorem solution {A : Finset ℝ²} (hK4 : HasNEquidistantProperty 4 A)
    {p : ℝ²} (hpA : p ∈ A) (hpExtra : 7 ≤ iCountAt A p) :
    6 * A.card + 1 ≤ iCount A := by
  classical
  unfold iCount
  rw [← Finset.sum_erase_add _ _ hpA]
  have hcard : A.card = (A.erase p).card + 1 := by
    rw [← card_insert_of_notMem]
    · rw [insert_erase hpA]
    · simp
  have hsum : 6 * (A.erase p).card ≤ ∑ q ∈ A.erase p, iCountAt A q := by
    calc
      6 * (A.erase p).card = ∑ _q ∈ A.erase p, 6 := by
        rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ q ∈ A.erase p, iCountAt A q := by
        refine sum_le_sum ?_
        intro q hq
        exact iCountAt_ge_six_of_K4 A q (hK4 q (mem_of_mem_erase hq))
  rw [hcard]
  calc
    6 * ((A.erase p).card + 1) + 1 = 6 * (A.erase p).card + 7 := by omega
    _ ≤ (∑ q ∈ A.erase p, iCountAt A q) + iCountAt A p :=
      Nat.add_le_add hsum hpExtra
