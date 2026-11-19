-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.hCanonicalizedInput_error_eq_one_sub_hFidelity_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:13:11.600005+00:00
-- url     : https://prove2.me/submissions/b40cf632-da45-4977-b396-bc2e99ac48eb

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hInputSquaredOverlap_eq_hInputFidelity_sq
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hCanonicalizedInput_hInputFidelity

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
    hInputError (hCanonicalizedInput rho) = 1 - hFidelity rho ^ 2 := by
  rw [hInputError, hInputSquaredOverlap_eq_hInputFidelity_sq,
    hCanonicalizedInput_hInputFidelity]
end QEC.Distillation.BK15.NoisyInput
