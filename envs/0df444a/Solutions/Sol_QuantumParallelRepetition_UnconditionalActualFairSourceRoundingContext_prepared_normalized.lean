-- Prove2me | solution 1 for QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext.prepared_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/024c45a8-c947-4b34-a27f-65d3b098f560

import Mathlib
import Definitions.Def_QuantumParallelRepetition
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
attribute [local instance] Classical.propDecidable
open QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
variable {D : Finset (Fin n)} {alpha gamma : ℝ}
namespace QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext
theorem _root_.solution
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    ∀ f : flag c, ‖prepared c f‖ = 1 := by
  intro f
  exact unconditionalSourcePhysicalCleanedStoppingFixedSource_norm
    c.stopping.phases c.stopping.grid (dimension_pos c)
    c.stopping.harmonic
end QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext
