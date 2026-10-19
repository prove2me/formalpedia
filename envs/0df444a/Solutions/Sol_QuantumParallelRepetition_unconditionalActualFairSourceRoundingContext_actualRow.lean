-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_actualRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/3e3f5b88-641c-43bc-809c-80466b7fecfb

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCleanedRow_le_one
import Theorems.Thm_QuantumParallelRepetition_UnconditionalActualFairSourceRoundingContext_dimension_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
open UnconditionalActualFairSourceRoundingContext
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (h : ExactLocallySampleableTuple X Y A B D) :
    (∑ j : Fin c.stopping.L, ‖actual c (h, j)‖ ^ 2) ≤ 1 := by
  exact unconditionalActualFairCleanedRow_le_one
    c.stopping.phases c.stopping.grid (dimension_pos c)
    c.stopping.harmonic (width c) (width_all c) (schedule c)
    (gammaVector c h) (phiVector c h)
    c.stopping.Q c.stopping.UA c.stopping.UB
end QuantumParallelRepetition
