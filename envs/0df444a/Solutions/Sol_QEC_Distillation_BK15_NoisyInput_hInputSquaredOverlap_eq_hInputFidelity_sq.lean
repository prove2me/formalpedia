-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.hInputSquaredOverlap_eq_hInputFidelity_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T00:59:05.901736+00:00
-- url     : https://prove2.me/submissions/a3d93dc9-c73b-43b5-8689-40918f1e7707

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hProjector_isSymmetricProjection
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_nonneg


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
    hInputSquaredOverlap rho = hInputFidelity rho ^ 2 := by
  unfold hInputSquaredOverlap hInputFidelity hDirectionFidelity projectionFidelity
  rw [Real.sq_sqrt]
  exact projectionSquaredOverlap_nonneg (hProjector hReference) rho
    (hProjector_isSymmetricProjection hReference)
end QEC.Distillation.BK15.NoisyInput
