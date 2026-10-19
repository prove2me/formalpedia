-- Prove2me | solution 1 for QuantumParallelRepetition.remainingCoordinates_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/88a44d3e-2eb3-4bf3-8ce6-6cb2549adb97

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    {n : ℕ} (C : Finset (Fin n)) :
    (Finset.univ \ C).card = n - C.card := by
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ C)]
end QuantumParallelRepetition
