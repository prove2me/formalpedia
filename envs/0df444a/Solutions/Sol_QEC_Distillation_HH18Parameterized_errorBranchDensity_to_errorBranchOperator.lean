-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.errorBranchDensity_to_errorBranchOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:58:30.758303+00:00
-- url     : https://prove2.me/submissions/e6034193-e95b-4c20-bcd6-3021b2906611

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchState_normSq


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
    (error : PhysicalErrorWord m w) :
    (DensityOperator.pureDensity (errorBranchState h hdegree error)
      (errorBranchState_normSq h hdegree error)).toOperator =
      errorBranchOperator h hdegree error := by
  rw [DensityOperator.pureDensity_toOperator]
  rfl
end QEC.Distillation.HH18Parameterized
