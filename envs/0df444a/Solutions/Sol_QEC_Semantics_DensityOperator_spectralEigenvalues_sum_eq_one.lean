-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.spectralEigenvalues_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:09:03.305459+00:00
-- url     : https://prove2.me/submissions/42575f50-a3b6-4de1-8db6-5b43dbeddaa2

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
    (∑ i, rho.spectralEigenvalues i : Real) = 1 := by
  have htrace := rho.positive.isSymmetric.re_trace_eq_sum_eigenvalues rfl
  rw [rho.trace_one] at htrace
  simpa [spectralEigenvalues] using htrace.symm
end QEC.Semantics.DensityOperator
