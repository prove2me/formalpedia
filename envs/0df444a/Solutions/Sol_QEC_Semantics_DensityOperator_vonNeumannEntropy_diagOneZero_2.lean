-- Prove2me | solution 2 for QEC.Semantics.DensityOperator.vonNeumannEntropy_diagOneZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:00.436203+00:00
-- url     : https://prove2.me/submissions/da351ced-e464-43cc-8b74-41d6b341d455

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_diagonalDensity
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



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
theorem _root_.solution : diagOneZero.vonNeumannEntropy = 0 := by
  rw [diagOneZero, vonNeumannEntropy_diagonalDensity]
  rw [Fin.sum_univ_two]
  simp
end QEC.Semantics.DensityOperator
