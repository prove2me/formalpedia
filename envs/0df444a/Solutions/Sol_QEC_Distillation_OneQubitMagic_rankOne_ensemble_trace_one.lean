-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.rankOne_ensemble_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:55:49.984868+00:00
-- url     : https://prove2.me/submissions/9d15bc5d-08b2-4987-8bfe-4f81c5c7ce1c

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
    (rho : DensityOperator QubitSpace) {m : Nat}
    (u : Fin m → QubitSpace)
    (hensemble : rho.toOperator =
      ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :
    ∑ i, inner Complex (u i) (u i) = 1 := by
  have htrace := rho.trace_one
  rw [hensemble] at htrace
  simpa [map_sum, InnerProductSpace.trace_rankOne] using htrace
end QEC.Distillation.OneQubitMagic
