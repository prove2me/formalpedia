-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionSquaredOverlap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:02:07.758581+00:00
-- url     : https://prove2.me/submissions/1a056921-96c1-4a3a-b391-eb2ffbea403a

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
    0 ≤ projectionSquaredOverlap P rho :=
  (projectionSquaredOverlap_mem_Icc P rho hP).1
end QEC.Distillation.OneQubitMagic
