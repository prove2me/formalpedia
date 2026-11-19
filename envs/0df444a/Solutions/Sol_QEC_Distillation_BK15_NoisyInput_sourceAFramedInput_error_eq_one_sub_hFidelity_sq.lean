-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.sourceAFramedInput_error_eq_one_sub_hFidelity_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:23:41.020482+00:00
-- url     : https://prove2.me/submissions/11bc8017-a4e2-4745-9fd4-b6cfe3c578af

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceAFramedInput_aInputSquaredOverlap

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
theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    aInputError (sourceAFramedInput rho) = 1 - hFidelity rho ^ 2 := by
  rw [aInputError, sourceAFramedInput_aInputSquaredOverlap]
end QEC.Distillation.BK15.NoisyInput
