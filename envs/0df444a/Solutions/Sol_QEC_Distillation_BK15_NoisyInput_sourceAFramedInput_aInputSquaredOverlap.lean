-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.sourceAFramedInput_aInputSquaredOverlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:21:11.149813+00:00
-- url     : https://prove2.me/submissions/46aa1673-a65c-4a32-8591-2cdc4295a4d8

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hInputSquaredOverlap_eq_hInputFidelity_sq
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hCanonicalizedInput_hInputFidelity
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceA0Transport_conj_hReference_projector
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_conjDensity


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
    aInputSquaredOverlap (sourceAFramedInput rho) = hFidelity rho ^ 2 := by
  unfold aInputSquaredOverlap sourceAFramedInput
  calc
    projectionSquaredOverlap (aBasisProjector .positive)
        (sourceA0Transport.conjDensity (hCanonicalizedInput rho)) =
        projectionSquaredOverlap
          (sourceA0Transport.conjOperator (hProjector hReference))
          (sourceA0Transport.conjDensity (hCanonicalizedInput rho)) := by
      rw [sourceA0Transport_conj_hReference_projector]
    _ = projectionSquaredOverlap (hProjector hReference)
          (hCanonicalizedInput rho) :=
      projectionSquaredOverlap_conjDensity sourceA0Transport
        (hProjector hReference) (hCanonicalizedInput rho)
    _ = hInputSquaredOverlap (hCanonicalizedInput rho) := rfl
    _ = hInputFidelity (hCanonicalizedInput rho) ^ 2 :=
      hInputSquaredOverlap_eq_hInputFidelity_sq (hCanonicalizedInput rho)
    _ = hFidelity rho ^ 2 := by rw [hCanonicalizedInput_hInputFidelity]
end QEC.Distillation.BK15.NoisyInput
