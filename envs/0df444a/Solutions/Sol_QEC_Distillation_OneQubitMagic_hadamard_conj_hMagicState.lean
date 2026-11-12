-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hadamard_conj_hMagicState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:17:27.977205+00:00
-- url     : https://prove2.me/submissions/14e710a3-72ed-4df4-af12-2cb74ede9c66

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_hProjector
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
theorem _root_.solution (d : HDirection) :
    hadamardTransport.conjDensity (hMagicStateOfDirection d) =
      hMagicStateOfDirection (hadamardClifford • d) := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator]
  change hadamardTransport.conjOperator (hProjector d) =
    hProjector (hadamardClifford • d)
  exact hadamard_conj_hProjector d
end QEC.Distillation.OneQubitMagic
