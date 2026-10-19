-- Prove2me | solution 1 for QuantumParallelRepetition.fullCoordinateAnswerExtension_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/5f6ee9d6-54bb-45aa-b395-5be087c22694

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
    {T R : Type*} [Fintype T] [AddCommMonoid R]
    {n : ℕ} (D : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (f : ({j : Fin n // j ∈ insert i D} → T) → R) :
    (∑ α : {j : Fin n // j ∈ insert i D} → T, f α) =
      ∑ α : {j : Fin n // j ∈ D} → T, ∑ a : T,
        f (fullCoordinateAnswerExtension D i α a) := by
  classical
  simpa [fullCoordinateAnswerExtensionEquiv, Fintype.sum_prod_type]
    using ((fullCoordinateAnswerExtensionEquiv
      (T := T) D i hiD).sum_comp f).symm
end QuantumParallelRepetition
