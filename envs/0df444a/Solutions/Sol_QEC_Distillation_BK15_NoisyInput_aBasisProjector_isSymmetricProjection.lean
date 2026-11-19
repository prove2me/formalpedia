-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.aBasisProjector_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:11:51.359806+00:00
-- url     : https://prove2.me/submissions/86805161-6031-4930-b6f7-1b86c9d74b59

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput

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
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) :
    (aBasisProjector outcome).IsSymmetricProjection := by
  refine ⟨aBasisProjector_idempotent outcome, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact aBasisProjector_adjoint outcome
end QEC.Distillation.BK15.NoisyInput
