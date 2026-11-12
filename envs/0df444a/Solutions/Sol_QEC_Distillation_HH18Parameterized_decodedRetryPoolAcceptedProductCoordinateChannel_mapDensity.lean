-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:19:23.925242+00:00
-- url     : https://prove2.me/submissions/619cae0c-a1d6-486a-98b5-f333a578205a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRegisterTrialChannel_mapDensity_transport
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (required : Nat) (block : Fin required) (port : LogicalSite m w) :
    (decodedRetryPoolAcceptedProductCoordinateChannel
      m w required block port).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon port := by
  rw [decodedRetryPoolAcceptedProductCoordinateChannel,
    QuantumChannel.comp_mapDensity]
  rw [decodedRetryPoolAcceptedProductDensity]
  rw [tensorPowerRegisterProductDensity]
  rw [tensorPowerRegisterTrialChannel_mapDensity_transport]
  rw [tensorPowerInputMarginal_productInput]
  exact decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
    m w port
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
end QEC.Distillation.HH18Parameterized
