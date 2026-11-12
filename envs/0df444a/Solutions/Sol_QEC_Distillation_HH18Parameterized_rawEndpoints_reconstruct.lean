-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.rawEndpoints_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:06:08.339876+00:00
-- url     : https://prove2.me/submissions/30944969-dc9a-4b04-b29a-970a2f15f835

import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
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

theorem solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    rawEndpoint h hdegree inputs .accepted + rawEndpoint h hdegree inputs .rejected =
      ((physicalOperation h hdegree).mapDensity
        (prepareMeasuredResources m w inputs)).toOperator := by
  have hsum := (postselectionInstrument h).sum_branchOperator_eq_mapDensity_toOperator
    (postselectionInstrument_complete h)
    (resourcePreSyndromeState h hdegree inputs)
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at hsum
  simpa [rawEndpoint, rawPostselectionEndpoint, rawPostselectionBranch,
    resourcePreSyndromeState, physicalOperation, QuantumChannel.comp_mapDensity] using hsum