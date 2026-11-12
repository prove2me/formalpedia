-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decoderChannel_rankOne_physicalTInv_eq_idealLogicalTOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:28:44.946851+00:00
-- url     : https://prove2.me/submissions/d773e5d9-5a89-4877-8672-f9fdf2209db1

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decoderChannel_rankOne_encoded
import Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalTInvBranch_eq_logicalT


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
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    decoderChannel h (InnerProductSpace.rankOne Complex
      (physicalTInvBranch h hdegree) (physicalTInvBranch h hdegree)).toLinearMap =
      (idealLogicalTOutput m w).toOperator := by
  rw [physicalTInvBranch_eq_logicalT h hdegree]
  change decoderChannel h (InnerProductSpace.rankOne Complex
    (ambientEncodingIsometry h (idealLogicalTOutputState m w))
    (ambientEncodingIsometry h (idealLogicalTOutputState m w))).toLinearMap = _
  rw [decoderChannel_rankOne_encoded]
  rfl
end QEC.Distillation.HH18Parameterized
