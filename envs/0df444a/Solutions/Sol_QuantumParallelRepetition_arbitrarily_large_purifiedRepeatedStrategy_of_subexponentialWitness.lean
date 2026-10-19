-- Prove2me | solution 1 for QuantumParallelRepetition.arbitrarily_large_purifiedRepeatedStrategy_of_subexponentialWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/ae7f64dc-b99e-480c-8197-170bb55cd0ad

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_entangledValue_le_one
import Theorems.Thm_QuantumParallelRepetition_not_hasExponentialBound_iff
import Theorems.Thm_QuantumParallelRepetition_arbitrarily_large_witness_of_not_hasExponentialBound
import Theorems.Thm_QuantumParallelRepetition_exists_purifiedRepeatedStrategy_of_lt_entangledValue

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
    (G : Game X Y A B)
    (hwitness : HasSubexponentialWitness (repeatedEntangledValue G))
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      ∃ S : Strategy (G.repeat n),
        Real.exp (-c * (n : ℝ)) <
          (purifiedStrategy S).winProbability := by
  have hno : ¬ HasExponentialBound (repeatedEntangledValue G) :=
    (not_hasExponentialBound_iff (repeatedEntangledValue G)).mpr hwitness
  have hbounded (n : ℕ) : repeatedEntangledValue G n ≤ 1 :=
    entangledValue_le_one (G.repeat n)
  obtain ⟨n, hn, hvalue⟩ :=
    arbitrarily_large_witness_of_not_hasExponentialBound
      hbounded hno hc N
  exact ⟨n, hn,
    exists_purifiedRepeatedStrategy_of_lt_entangledValue G
      (Real.exp_pos _) hvalue⟩
end QuantumParallelRepetition
