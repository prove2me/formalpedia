-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_trace_entropyFunctionalCalculus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:29.894106+00:00
-- url     : https://prove2.me/submissions/fa7351a1-8b4e-4be0-ac5e-ce95e3c3ffa0

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_basisMatrixSpectrum
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
theorem _root_.solution
    (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (rho.vonNeumannEntropy : Complex) =
      Matrix.trace ((rho.spectralMatrix_isHermitian b).cfc entropyTerm) := by
  let A := rho.spectralMatrix b
  let hA : A.IsHermitian := rho.spectralMatrix_isHermitian b
  change (rho.vonNeumannEntropy : Complex) = Matrix.trace (hA.cfc entropyTerm)
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rw [rho.vonNeumannEntropy_eq_basisMatrixSpectrum b]
  change
    (((A.charpoly.roots.map Complex.re).map entropyTerm).sum : Complex) =
      ∑ i, (entropyTerm (hA.eigenvalues i) : Complex)
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp [Function.comp_def, List.sum_ofFn]
end QEC.Semantics.DensityOperator
