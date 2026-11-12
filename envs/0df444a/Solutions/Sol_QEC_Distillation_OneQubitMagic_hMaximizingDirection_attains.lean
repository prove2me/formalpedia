-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hMaximizingDirection_attains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:18:43.017858+00:00
-- url     : https://prove2.me/submissions/b4dd4f7d-0cbc-40ff-afb2-b4083500765d

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
    hFidelity rho = hDirectionFidelity rho (hMaximizingDirection rho) :=
  Classical.choose_spec (exists_hDirection_attaining_fidelity rho)
end QEC.Distillation.OneQubitMagic
