-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.trace_mul_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:55:53.253417+00:00
-- url     : https://prove2.me/submissions/83b9fa8a-1919-4b00-b4fa-edaa02658e75

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
    (P : Operator QubitSpace) (u : QubitSpace) :
    LinearMap.trace Complex QubitSpace
      (P * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
      inner Complex u (P u) := by
  have hcomp :
      P.comp (InnerProductSpace.rankOne Complex u u).toLinearMap =
        (InnerProductSpace.rankOne Complex (P u) u).toLinearMap := by
    ext z
    simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply]
  change LinearMap.trace Complex QubitSpace
      (P.comp (InnerProductSpace.rankOne Complex u u).toLinearMap) = _
  rw [hcomp, InnerProductSpace.trace_rankOne]
end QEC.Distillation.OneQubitMagic
