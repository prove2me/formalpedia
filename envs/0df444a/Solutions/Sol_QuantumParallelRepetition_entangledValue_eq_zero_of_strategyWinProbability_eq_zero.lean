-- Prove2me | solution 1 for QuantumParallelRepetition.entangledValue_eq_zero_of_strategyWinProbability_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/aea1a4ac-d858-436d-9a3d-712ae072ebc5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_entangledValue_nonneg

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
    (hzero : ∀ S : Strategy G, S.winProbability = 0) :
    entangledValue G = 0 := by
  apply le_antisymm _ (entangledValue_nonneg G)
  unfold entangledValue
  by_cases hnonempty :
      (Set.range (Strategy.winProbability (G := G))).Nonempty
  · apply csSup_le hnonempty
    rintro _ ⟨S, rfl⟩
    exact le_of_eq (hzero S)
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty,
      Real.sSup_empty]
end QuantumParallelRepetition
