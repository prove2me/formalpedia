-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionSquaredOverlap_conjDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:58:37.75839+00:00
-- url     : https://prove2.me/submissions/facf6c21-7833-4765-aa53-92ef161c34ee

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (U : UnitaryTransport QubitSpace QubitSpace)
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) :
    projectionSquaredOverlap (U.conjOperator P) (U.conjDensity rho) =
      projectionSquaredOverlap P rho := by
  unfold projectionSquaredOverlap
  rw [UnitaryTransport.conjDensity_toOperator,
    ← UnitaryTransport.conjOperator_mul,
    UnitaryTransport.trace_conjOperator]
end QEC.Distillation.OneQubitMagic
