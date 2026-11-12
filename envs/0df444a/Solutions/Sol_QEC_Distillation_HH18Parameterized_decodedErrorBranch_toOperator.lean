-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedErrorBranch_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:37:08.174902+00:00
-- url     : https://prove2.me/submissions/931b5f0b-45cd-4710-9431-4580aedf36cb

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchDensity_to_errorBranchOperator
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
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    (decodedErrorBranch h hdegree error).toOperator =
      decoderChannel h (errorBranchOperator h hdegree error) := by
  change decoderChannel h
      (DensityOperator.pureDensity (errorBranchState h hdegree error)
        (errorBranchState_normSq h hdegree error)).toOperator = _
  rw [errorBranchDensity_to_errorBranchOperator h hdegree error]
end QEC.Distillation.HH18Parameterized
