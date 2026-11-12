-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionFidelity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:55:59.968731+00:00
-- url     : https://prove2.me/submissions/4b56ea58-42b1-4ad4-9fc9-3059b8e7873c

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) :
    0 ≤ projectionFidelity P rho := by
  exact Real.sqrt_nonneg _
end QEC.Distillation.OneQubitMagic
