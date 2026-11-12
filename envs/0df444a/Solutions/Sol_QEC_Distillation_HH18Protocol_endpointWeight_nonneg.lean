-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.endpointWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:14:59.80984+00:00
-- url     : https://prove2.me/submissions/ff0c2e46-ee40-492f-a673-6deb74bbf1f5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome) : 0 ≤ endpointWeight inputs outcome :=
  HH18Postselection.postselectionInstrument.bornWeight_nonneg outcome _
end QEC.Distillation.HH18Protocol
