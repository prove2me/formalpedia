-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionFidelity_conjDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:00:28.311062+00:00
-- url     : https://prove2.me/submissions/b4077958-a94d-4e51-97c1-ee0735a55e43

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_conjDensity

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
    projectionFidelity (U.conjOperator P) (U.conjDensity rho) =
      projectionFidelity P rho := by
  unfold projectionFidelity
  rw [projectionSquaredOverlap_conjDensity]
end QEC.Distillation.OneQubitMagic
