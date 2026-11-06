-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_diagHalfHalf
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:44:52.569265+00:00
-- url     : https://prove2.me/submissions/db30df26-9895-4d9d-9359-ad6ddf6f8778

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_diagonalDensity
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem solution : diagHalfHalf.vonNeumannEntropy = 1 := by
  rw [diagHalfHalf, vonNeumannEntropy_diagonalDensity]
  rw [Fin.sum_univ_two]
  change entropyTerm (1 / 2 : Real) + entropyTerm (1 / 2 : Real) = 1
  rw [entropyTerm_half]
  norm_num
