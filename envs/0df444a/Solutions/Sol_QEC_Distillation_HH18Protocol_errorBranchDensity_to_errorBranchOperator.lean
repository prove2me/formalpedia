-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.errorBranchDensity_to_errorBranchOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:10:59.390956+00:00
-- url     : https://prove2.me/submissions/61b419e4-c9f7-421f-bc3c-1e62a393b967

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceChannel
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Semantics
open Semantics.Qubit
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (error : PhysicalErrorWord) :
    (DensityOperator.pureDensity (errorBranchState error)
      (errorBranchState_normSq error)).toOperator =
      HH18SyndromeDecoding.errorBranchOperator error := by
  rw [DensityOperator.pureDensity_toOperator]
  rfl
end QEC.Distillation.HH18Protocol
