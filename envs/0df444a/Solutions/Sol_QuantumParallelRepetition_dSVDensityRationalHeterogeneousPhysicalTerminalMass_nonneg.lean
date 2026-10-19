-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousPhysicalTerminalMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/93675148-0cec-4dbd-97e7-fb0720dec9c3

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalTerminalMass
      N width schedule ξ ζ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
    N width schedule ξ ζ L
end QuantumParallelRepetition
