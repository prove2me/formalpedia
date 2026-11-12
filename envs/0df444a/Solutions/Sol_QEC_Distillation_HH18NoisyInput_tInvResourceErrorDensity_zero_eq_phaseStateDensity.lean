-- Prove2me | solution 1 for QEC.Distillation.HH18NoisyInput.tInvResourceErrorDensity_zero_eq_phaseStateDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:39:22.42678+00:00
-- url     : https://prove2.me/submissions/c6d74d92-f811-44d0-a3c5-7f434bb674d1

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18NoisyInput
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
universe u
namespace QEC.Distillation.HH18NoisyInput
theorem _root_.solution :
    tInvResourceErrorDensity 0 = OneQubitMagic.phaseStateDensity (-Real.pi / 4) :=
  tInvResourceErrorDensity_zero
end QEC.Distillation.HH18NoisyInput
