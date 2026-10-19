-- Prove2me | solution 1 for QuantumParallelRepetition.exactLocallySampleableLaw_psi_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/638309a8-ebdd-4f50-86a2-a6a22653d449

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_coordinate_eq_of_ne_zero
import Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_accepted_of_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactUnnormalizedPsi
      G n S D t.2.2.2 t.2.1 t.2.2.1 ≠ 0 := by
  classical
  have coordinate :=
    exactLocallySampleableLaw_coordinate_eq_of_ne_zero
      G n S D t supported
  have accepted :=
    exactLocallySampleableLaw_accepted_of_ne_zero
      G n S D t supported
  intro zero
  apply supported
  have source :=
    exactLocallySampleableLaw_eq_fair_born
      G n S D t.2.2.2 t.2.1 t.2.2.1
  have tuple :
      t =
        (t.2.2.2.seed.coordinate, t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa using coordinate
  rw [tuple, source, if_pos accepted, zero]
  simp
end QuantumParallelRepetition
