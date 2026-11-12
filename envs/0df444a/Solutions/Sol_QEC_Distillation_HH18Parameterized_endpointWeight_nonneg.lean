-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.endpointWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:27:05.381285+00:00
-- url     : https://prove2.me/submissions/aaec11c0-9a46-4e55-820e-aff7a5ad756a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionWeight_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    0 ≤ endpointWeight h hdegree inputs outcome :=
  postselectionWeight_nonneg h outcome (resourcePreSyndromeState h hdegree inputs)
end QEC.Distillation.HH18Parameterized
