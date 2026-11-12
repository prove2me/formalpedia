-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionSquaredOverlap_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:02:27.387814+00:00
-- url     : https://prove2.me/submissions/5ac013eb-fefc-433d-a349-6b3f4bc9bce1

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_mem_Icc

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace)
    (hP : P.IsSymmetricProjection) :
    projectionSquaredOverlap P rho ≤ 1 :=
  (projectionSquaredOverlap_mem_Icc P rho hP).2
end QEC.Distillation.OneQubitMagic
