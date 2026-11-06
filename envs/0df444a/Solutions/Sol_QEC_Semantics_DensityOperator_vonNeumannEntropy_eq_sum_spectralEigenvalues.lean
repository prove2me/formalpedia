-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_sum_spectralEigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:30.270005+00:00
-- url     : https://prove2.me/submissions/584017f2-42c4-4afa-95b1-ef54e9a830ca

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
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
theorem _root_.solution (rho : DensityOperator H) :
    rho.vonNeumannEntropy = ∑ i, entropyTerm (rho.spectralEigenvalues i) := by
  unfold vonNeumannEntropy finiteSpectrum spectralEigenvalues
  rw [rho.positive.isSymmetric.roots_charpoly_eq_eigenvalues rfl]
  simp [Function.comp_def, List.sum_ofFn]
end QEC.Semantics.DensityOperator
