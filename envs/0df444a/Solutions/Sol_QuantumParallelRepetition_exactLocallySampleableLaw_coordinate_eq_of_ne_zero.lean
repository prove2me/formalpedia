-- Prove2me | solution 1 for QuantumParallelRepetition.exactLocallySampleableLaw_coordinate_eq_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/e193e1d4-fb4d-463d-8137-8c85dbd9b0fd

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    t.1 = t.2.2.2.seed.coordinate := by
  classical
  by_contra different
  apply supported
  unfold exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_eq_zero
  intro q member
  have code :
      exactLocallySampleableCode D q = t := by
    exact ((@Finset.mem_filter
      (ExactJointOutcome X Y A B D)
      (fun a => exactLocallySampleableCode D a = t)
      (fun _ => Classical.propDecidable _)
      Finset.univ q).mp member).2
  have coordinate :=
    congrArg
      (fun u : ExactLocallySampleableTuple X Y A B D =>
        u.1)
      code
  have history_coordinate :=
    congrArg
      (fun u : ExactLocallySampleableTuple X Y A B D =>
        u.2.2.2.seed.coordinate)
      code
  exact False.elim
    (different (coordinate.symm.trans history_coordinate))
end QuantumParallelRepetition
