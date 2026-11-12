-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.rawEndpoints_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:56:24.623207+00:00
-- url     : https://prove2.me/submissions/0b65d85a-19de-4389-91c7-5fc7be291656

import Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
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

theorem solution
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