-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateInsertedHistory_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/a22dbd3f-bf9b-47a9-a3e6-7277abff4640

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (f : FullSubsetHistory X Y n (insert i D) L → T) :
    (∑ h : FullSubsetHistory X Y n (insert i D) L, f h) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
        f (fullCoordinateInsertedHistory D L i r x y) := by
  classical
  simpa [fullCoordinateInsertedHistoryEquiv, Fintype.sum_prod_type]
    using ((fullCoordinateInsertedHistoryEquiv
      (X := X) (Y := Y) D L i hiD).sum_comp f).symm
end QuantumParallelRepetition
