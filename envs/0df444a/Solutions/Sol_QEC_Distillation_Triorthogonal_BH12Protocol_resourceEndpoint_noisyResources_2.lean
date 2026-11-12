-- Prove2me | solution 2 for QEC.Distillation.Triorthogonal.BH12Protocol.resourceEndpoint_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:43:57.165365+00:00
-- url     : https://prove2.me/submissions/a5795a1f-ec28-4633-86cb-7adb6e5fe73c

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol

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
    (p : ErrorParameter) (outcome : DistillationOutcome) :
    resourceEndpoint q (noisyResources q p) outcome = rawEndpoint q p outcome := by
  unfold resourceEndpoint rawEndpoint
  rw [resourcePreSyndromeState_noisyResources]
end QEC.Distillation.Triorthogonal.BH12Protocol
