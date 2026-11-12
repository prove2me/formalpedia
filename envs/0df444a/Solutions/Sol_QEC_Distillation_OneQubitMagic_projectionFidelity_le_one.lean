-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.projectionFidelity_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:04:29.851723+00:00
-- url     : https://prove2.me/submissions/1ea29e87-629f-407d-809b-4d2bae8e32f1

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_le_one

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
    projectionFidelity P rho ≤ 1 := by
  rw [projectionFidelity, Real.sqrt_le_one]
  exact projectionSquaredOverlap_le_one P rho hP
end QEC.Distillation.OneQubitMagic
