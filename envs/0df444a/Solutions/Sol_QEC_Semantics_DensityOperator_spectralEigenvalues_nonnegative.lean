-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.spectralEigenvalues_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:09:19.69417+00:00
-- url     : https://prove2.me/submissions/4b404a4f-055e-47bf-8617-8f500d28fc9e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional

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
theorem _root_.solution (rho : DensityOperator H)
    (i : Fin (Module.finrank Complex H)) :
    0 <= rho.spectralEigenvalues i := by
  exact rho.positive.nonneg_eigenvalues rfl i
end QEC.Semantics.DensityOperator
