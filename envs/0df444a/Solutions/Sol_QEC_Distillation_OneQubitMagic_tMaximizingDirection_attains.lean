-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tMaximizingDirection_attains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:58:19.69503+00:00
-- url     : https://prove2.me/submissions/f50c40aa-0fbf-4ff0-ac1b-18b29436b6eb

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
    (rho : DensityOperator QubitSpace) :
    tFidelity rho = tDirectionFidelity rho (tMaximizingDirection rho) :=
  Classical.choose_spec (exists_tDirection_attaining_fidelity rho)
end QEC.Distillation.OneQubitMagic
