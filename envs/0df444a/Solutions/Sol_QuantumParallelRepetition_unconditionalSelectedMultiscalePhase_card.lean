-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedMultiscalePhase_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/ff2715d9-24d8-476e-be01-a232470af1d5

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    (S B : ℕ) :
    Fintype.card
        (DSVDensityRationalPublicMultiscalePhase (S + 1) B) =
      B * Fintype.card (Fin S → Fin B) := by
  simp [DSVDensityRationalPublicMultiscalePhase,
    pow_succ, Nat.mul_comm]
end QuantumParallelRepetition
