-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedPath_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:05:38.55945+00:00
-- url     : https://prove2.me/submissions/af64476c-9ab0-460b-a744-1d52e6a761c9

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
import Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPath_card


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w depth : Nat) :
    Fintype.card (nestedTensorPath (logicalOutputCount m w) depth) =
      logicalOutputCount m w ^ depth :=
  nestedTensorPath_card (logicalOutputCount m w) depth
end QEC.Distillation.HH18Parameterized
