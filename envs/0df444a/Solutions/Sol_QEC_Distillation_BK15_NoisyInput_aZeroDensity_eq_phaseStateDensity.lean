-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.aZeroDensity_eq_phaseStateDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:00.510637+00:00
-- url     : https://prove2.me/submissions/21504bd3-1ee2-41f9-898c-61b4c4d0e5d5

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceA0Density_eq_phaseStateDensity

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.BK15.NoisyInput
theorem _root_.solution :
    aZeroDensity = phaseStateDensity (Real.pi / 4) :=
  sourceA0Density_eq_phaseStateDensity
end QEC.Distillation.BK15.NoisyInput
