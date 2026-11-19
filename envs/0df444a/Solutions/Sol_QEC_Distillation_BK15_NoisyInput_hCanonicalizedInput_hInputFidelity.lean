-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.hCanonicalizedInput_hInputFidelity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:50.036477+00:00
-- url     : https://prove2.me/submissions/4e19cfaf-5b2e-49a8-9a46-49f5cd9b1fde

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hCanonicalizer_conj_hProjector
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hMaximizingDirection_attains
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionFidelity_conjDensity


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
theorem _root_.solution (rho : DensityOperator QubitSpace) :
    hInputFidelity (hCanonicalizedInput rho) = hFidelity rho := by
  unfold hCanonicalizedInput hInputFidelity hDirectionFidelity
  rw [← hCanonicalizer_conj_hProjector (hMaximizingDirection rho)]
  rw [projectionFidelity_conjDensity]
  exact (hMaximizingDirection_attains rho).symm
end QEC.Distillation.BK15.NoisyInput
