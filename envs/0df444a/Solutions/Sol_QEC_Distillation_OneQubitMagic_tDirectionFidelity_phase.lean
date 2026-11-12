-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tDirectionFidelity_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:02:34.42962+00:00
-- url     : https://prove2.me/submissions/51d53d8f-7285-44a0-95df-212b1e346ed8

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_tProjector
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionFidelity_conjDensity
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
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    tDirectionFidelity (phaseTransport.conjDensity rho)
        (phaseClifford • d) =
      tDirectionFidelity rho d := by
  simpa only [tDirectionFidelity, phase_conj_tProjector] using
    projectionFidelity_conjDensity phaseTransport (tProjector d) rho
end QEC.Distillation.OneQubitMagic
