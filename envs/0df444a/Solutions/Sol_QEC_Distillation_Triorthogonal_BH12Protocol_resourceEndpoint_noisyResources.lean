-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.resourceEndpoint_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:03:00.518832+00:00
-- url     : https://prove2.me/submissions/ddb0398d-7f2e-4856-a2f6-563784b58d35

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

theorem solution (q : Nat)
    (p : ErrorParameter) (outcome : DistillationOutcome) :
    resourceEndpoint q (noisyResources q p) outcome = rawEndpoint q p outcome := by
  unfold resourceEndpoint rawEndpoint
  rw [resourcePreSyndromeState_noisyResources]