-- Prove2me | solution 1 for QuantumParallelRepetition.pdfConstantStrategy_outcomeProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/dee4d82b-6efd-446c-aa09-f7a8781ecc6d

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (a : A) (b : B)
    (x : X) (y : Y) (a' : A) (b' : B) :
    (pdfConstantStrategy G a b).outcomeProbability x y a' b' =
      if a' = a ∧ b' = b then 1 else 0 := by
  classical
  change
    (Matrix.trace
      ((1 : Matrix (PUnit × PUnit) (PUnit × PUnit) ℂ) *
        ((if a' = a then (1 : Matrix PUnit PUnit ℂ) else 0) ⊗ₖ
          (if b' = b then (1 : Matrix PUnit PUnit ℂ) else 0)))).re = _
  by_cases alice : a' = a <;> by_cases bob : b' = b <;>
    simp [alice, bob, Matrix.trace_one]
end QuantumParallelRepetition
