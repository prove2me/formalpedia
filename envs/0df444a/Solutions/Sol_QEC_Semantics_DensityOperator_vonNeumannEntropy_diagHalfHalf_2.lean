-- Prove2me | solution 2 for QEC.Semantics.DensityOperator.vonNeumannEntropy_diagHalfHalf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:10.718273+00:00
-- url     : https://prove2.me/submissions/fb61e3c0-0f7a-44b4-979e-54ed7d5a63fb

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
namespace QEC.Semantics.DensityOperator
theorem _root_.solution : diagHalfHalf.vonNeumannEntropy = 1 := by
  rw [diagHalfHalf, vonNeumannEntropy_diagonalDensity]
  rw [Fin.sum_univ_two]
  change entropyTerm (1 / 2 : Real) + entropyTerm (1 / 2 : Real) = 1
  rw [entropyTerm_half]
  norm_num
end QEC.Semantics.DensityOperator
