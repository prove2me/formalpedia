-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phase_conj_hMagicState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:17:31.157672+00:00
-- url     : https://prove2.me/submissions/69d3b4ba-1f12-4ba7-a0e6-af6698035c6f

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_hProjector
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
    phaseTransport.conjDensity (hMagicStateOfDirection d) =
      hMagicStateOfDirection (phaseClifford • d) := by
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator]
  change phaseTransport.conjOperator (hProjector d) =
    hProjector (phaseClifford • d)
  exact phase_conj_hProjector d
end QEC.Distillation.OneQubitMagic
