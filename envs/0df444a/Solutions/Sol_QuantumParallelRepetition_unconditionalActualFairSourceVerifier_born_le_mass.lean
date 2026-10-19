-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceVerifier_born_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/9b292af9-7e80-4c05-890c-6b45bcfddfc4

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_positive_complement_quadraticExpectation_le
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceVerifier_complement_isPositive

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
    quadraticExpectation
      (integratorActualC485WinningEffect
        (P := P) (N := N) (m := m)
        G n S D a₀ b₀ j x y) z ≤ ‖z‖ ^ 2 :=
  positive_complement_quadraticExpectation_le _
    (unconditionalActualFairSourceVerifier_complement_isPositive
      G n S D a₀ b₀ j x y) z
end QuantumParallelRepetition
