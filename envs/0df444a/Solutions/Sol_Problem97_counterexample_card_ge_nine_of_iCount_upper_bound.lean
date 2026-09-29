-- Prove2me | solution 1 for Problem97.counterexample_card_ge_nine_of_iCount_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T01:44:30.346475+00:00
-- url     : https://prove2.me/submissions/019dc6d2-055f-44ad-998d-07ed5bc7baa2

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna
-/

import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Theorems.Thm_Problem97_card_ge_five_of_K4
import Theorems.Thm_Problem97_counting_arithmetic
import Theorems.Thm_Problem97_six_mul_card_le_iCount_of_K4

section Erdos9796CountingFragment_Erdos9796Proof_P97_Counting

open scoped EuclideanGeometry
open Problem97

/-!
# Conditional counting assembly for the nine-point lower bound

Attribution to Dumitrescu records the isosceles-count method used by this
assembly. The quadratic upper bound is an input hypothesis, so this module
does not claim that upper bound itself.
-/

theorem solution
    {A : Finset ℝ²} (hne : A.Nonempty) (_hconv : ConvexIndep A)
    (hK4 : HasNEquidistantProperty 4 A)
    (hup : (iCount A : ℝ) ≤ ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12) :
    9 ≤ A.card := by
  have h5 : 5 ≤ A.card := card_ge_five_of_K4 hne hK4
  have h3 : 3 ≤ A.card := by omega
  -- Lower: 6 * A.card ≤ iCount A (ℕ).
  have hlo : 6 * A.card ≤ iCount A := six_mul_card_le_iCount_of_K4 hK4
  have hlor : (6 : ℝ) * A.card ≤ (iCount A : ℝ) := by exact_mod_cast hlo
  -- Upper: `iCount A` is bounded above by the quadratic expression.
  have hchain : (6 : ℝ) * A.card ≤ ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 :=
    hlor.trans hup
  exact counting_arithmetic h3 hchain

end Erdos9796CountingFragment_Erdos9796Proof_P97_Counting
