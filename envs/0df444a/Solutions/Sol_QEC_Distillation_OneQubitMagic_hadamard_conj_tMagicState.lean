-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hadamard_conj_tMagicState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:06:52.198441+00:00
-- url     : https://prove2.me/submissions/fab2a25d-e12b-4aa0-b573-810ada04a4b2

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_tProjector
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
private theorem densityOperator_ext {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
end OneQubitMagic
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (d : TDirection) :
    hadamardTransport.conjDensity (tMagicStateOfDirection d) =
      tMagicStateOfDirection (hadamardClifford • d) := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator]
  change hadamardTransport.conjOperator (tProjector d) =
    tProjector (hadamardClifford • d)
  exact hadamard_conj_tProjector d
end QEC.Distillation.OneQubitMagic
