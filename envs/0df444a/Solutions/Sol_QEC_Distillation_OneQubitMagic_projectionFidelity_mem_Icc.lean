-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionFidelity_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:06:58.452095+00:00
-- url     : https://prove2.me/submissions/968f03fe-ab6a-466d-83af-2a0672f29faa

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionFidelity_nonneg
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionFidelity_le_one

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
    projectionFidelity P rho ∈ Set.Icc 0 1 :=
  ⟨projectionFidelity_nonneg P rho,
    projectionFidelity_le_one P rho hP⟩
end QEC.Distillation.OneQubitMagic
