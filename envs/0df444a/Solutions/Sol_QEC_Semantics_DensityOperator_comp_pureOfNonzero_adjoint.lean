-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.comp_pureOfNonzero_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:17:41.945447+00:00
-- url     : https://prove2.me/submissions/3907736a-1ffa-41db-a7ba-ae7512528978

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (A : Operator H) (x : H) (hx : x ≠ 0) :
    A.comp ((pureOfNonzero x hx).toOperator.comp (LinearMap.adjoint A)) =
      (inner Complex x x)⁻¹ •
        (((InnerProductSpace.rankOne Complex (A x) (A x) : H →L[Complex] H) :
          H →ₗ[Complex] H)) := by
  ext y
  simp [pureOfNonzero, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
end QEC.Semantics.DensityOperator
