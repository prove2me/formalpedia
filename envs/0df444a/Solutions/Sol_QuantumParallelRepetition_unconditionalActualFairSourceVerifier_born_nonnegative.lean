-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceVerifier_born_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/e6302aea-f005-4e68-8594-cb80489b2bb4

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_positive_quadraticExpectation_nonneg
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceVerifier_isPositive

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y)
    (z : IntegratorActualC485BranchSpace
      1 P N
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        L m j) :
    0 ≤ quadraticExpectation
      (integratorActualC485WinningEffect
        (P := P) (N := N) (m := m)
        G n S D a₀ b₀ j x y) z :=
  positive_quadraticExpectation_nonneg _
    (unconditionalActualFairSourceVerifier_isPositive
      G n S D a₀ b₀ j x y) z
end QuantumParallelRepetition
