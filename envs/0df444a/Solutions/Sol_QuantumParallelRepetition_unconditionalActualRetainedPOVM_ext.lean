-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualRetainedPOVM_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/5f6b945c-49b4-4f3e-b441-50969bd7d053

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {C ι : Type*} [Fintype C] [Fintype ι] [DecidableEq ι]
    (P Q : POVM C ι)
    (same : ∀ (a : C) (i j : ι), P.effect a i j = Q.effect a i j) :
    P = Q := by
  cases P with
  | mk pe pp pc =>
    cases Q with
    | mk qe qp qc =>
      have effect : pe = qe := by
        funext a
        apply Matrix.ext
        intro i j
        exact same a i j
      cases effect
      rfl
end QuantumParallelRepetition
