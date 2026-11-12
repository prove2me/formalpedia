-- Prove2me | solution 2 for QEC.Distillation.HH18Protocol.rawEndpoints_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:31:36.118942+00:00
-- url     : https://prove2.me/submissions/e572aad1-34f4-4047-b618-4f8855856027

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator


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
    (inputs : ResourceInput resourceCount QubitSpace) :
    rawEndpoint inputs .accepted + rawEndpoint inputs .rejected =
      (physicalOperation.mapDensity (prepareMeasuredResources inputs)).toOperator := by
  have h := HH18Postselection.postselectionInstrument.sum_branchOperator_eq_mapDensity_toOperator
    HH18Postselection.postselectionInstrument_complete
    (resourcePreSyndromeState inputs)
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at h
  rw [Finset.sum_pair (by decide)] at h
  unfold physicalOperation
  rw [QuantumChannel.comp_mapDensity]
  exact h
end QEC.Distillation.HH18Protocol
