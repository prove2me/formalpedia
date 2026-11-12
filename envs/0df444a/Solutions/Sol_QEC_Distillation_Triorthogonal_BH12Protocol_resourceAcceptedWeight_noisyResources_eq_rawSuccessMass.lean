-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.resourceAcceptedWeight_noisyResources_eq_rawSuccessMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:03:38.268879+00:00
-- url     : https://prove2.me/submissions/227201a1-d0dd-4c9d-897b-9ca3346fb54a

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_endpointWeight_accepted_eq_rawSuccessMass

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
    (p : ErrorParameter) :
    resourceEndpointWeight q (noisyResources q p) .accepted = rawSuccessMass q p := by
  rw [resourceEndpointWeight_noisyResources,
    endpointWeight_accepted_eq_rawSuccessMass]
end QEC.Distillation.Triorthogonal.BH12Protocol
