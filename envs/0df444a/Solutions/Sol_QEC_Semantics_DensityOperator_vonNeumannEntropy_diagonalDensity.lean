-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_diagonalDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:19.127719+00:00
-- url     : https://prove2.me/submissions/19805f5a-3dd1-4f13-9e6b-5f61fe8a4e51

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Theorems.Thm_QEC_Semantics_DensityOperator_diagonalDensity_charpoly
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
theorem _root_.solution (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).vonNeumannEntropy = ∑ i, entropyTerm (p i) := by
  unfold vonNeumannEntropy finiteSpectrum
  rw [diagonalDensity_charpoly]
  rw [Matrix.charpoly_diagonal]
  rw [Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp [Function.comp_def, List.sum_ofFn]
end QEC.Semantics.DensityOperator
