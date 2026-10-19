-- Prove2me | solution 1 for QuantumParallelRepetition.exists_purifiedRepeatedStrategy_of_lt_entangledValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/313c2984-7ad9-40c3-a5f5-7a31f0fdfa3f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_purifiedStrategy_winProbability
import Theorems.Thm_QuantumParallelRepetition_exists_repeatedStrategy_of_lt_entangledValue

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hvalue : r < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n),
      r < (purifiedStrategy S).winProbability := by
  obtain ⟨S, hS⟩ :=
    exists_repeatedStrategy_of_lt_entangledValue G hr hvalue
  refine ⟨S, ?_⟩
  rwa [purifiedStrategy_winProbability]
end QuantumParallelRepetition
