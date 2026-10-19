-- Prove2me | solution 1 for QuantumParallelRepetition.not_hasExponentialBound_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/07b543da-b4a9-41f6-8124-baecb359e3ed

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
namespace QuantumParallelRepetition
theorem _root_.solution (v : ℕ → ℝ) :
    ¬ HasExponentialBound v ↔ HasSubexponentialWitness v := by
  simp [HasExponentialBound, HasSubexponentialWitness]
end QuantumParallelRepetition
