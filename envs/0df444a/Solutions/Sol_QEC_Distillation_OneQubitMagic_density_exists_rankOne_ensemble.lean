-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.density_exists_rankOne_ensemble
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:54:38.037866+00:00
-- url     : https://prove2.me/submissions/0edcfb28-8548-4557-9cdc-868bcb33e605

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    ∃ (m : Nat) (u : Fin m → QubitSpace),
      rho.toOperator =
        ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
  have hpositive :
      (LinearMap.toContinuousLinearMap rho.toOperator).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff rho.toOperator).2 rho.positive
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with
    ⟨m, u, hu⟩
  refine ⟨m, u, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap hu
end QEC.Distillation.OneQubitMagic
