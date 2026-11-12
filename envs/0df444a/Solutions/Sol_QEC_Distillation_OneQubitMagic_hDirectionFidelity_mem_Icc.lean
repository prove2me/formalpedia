-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hDirectionFidelity_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:10:35.658241+00:00
-- url     : https://prove2.me/submissions/cdde601f-98da-4ad7-8f02-c0173f4b967e

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionFidelity_mem_Icc
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hProjector_isSymmetricProjection

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (rho : DensityOperator QubitSpace) (d : HDirection) :
    hDirectionFidelity rho d ∈ Set.Icc 0 1 := by
  unfold hDirectionFidelity
  exact projectionFidelity_mem_Icc (hProjector d) rho
    (hProjector_isSymmetricProjection d)
end QEC.Distillation.OneQubitMagic
