-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.resourceAcceptedOutput_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:46:42.886481+00:00
-- url     : https://prove2.me/submissions/d33d2d16-543c-42d6-9aba-ec1b95e5c035

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceEndpoint_noisyResources
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) (hpos : 0 < endpointWeight q p .accepted) :
    resourceAcceptedOutput q (noisyResources q p)
        (by
          rw [resourceEndpointWeight_noisyResources]
          exact hpos) =
      (decoderChannel q).mapDensity (endpointConditional q p .accepted hpos) := by
  unfold resourceAcceptedOutput
  apply congrArg (decoderChannel q).mapDensity
  apply DensityOperator.ext_toOperator
  rw [resourceEndpointConditional_toOperator, endpointConditional_toOperator]
  rw [resourceEndpointWeight_noisyResources,
    resourceEndpoint_noisyResources]
end QEC.Distillation.Triorthogonal.BH12Protocol
