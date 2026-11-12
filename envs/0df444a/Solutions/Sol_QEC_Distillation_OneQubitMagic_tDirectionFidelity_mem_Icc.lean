-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tDirectionFidelity_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:10:09.959236+00:00
-- url     : https://prove2.me/submissions/990d843b-b259-4e6d-9393-c75564d59f6e

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionFidelity_mem_Icc
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tProjector_isSymmetricProjection

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    tDirectionFidelity rho d ∈ Set.Icc 0 1 := by
  unfold tDirectionFidelity
  exact projectionFidelity_mem_Icc (tProjector d) rho
    (tProjector_isSymmetricProjection d)
end QEC.Distillation.OneQubitMagic
