-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathStageRate_le_errorEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:46:21.975684+00:00
-- url     : https://prove2.me/submissions/63dd4bfe-307a-4d7f-a079-3786f5be3fe7

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_le_errorEnvelope


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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathRate h hdegree epsilon hsmall stage.1
      (routedDepthPathStagePath m w depth path stage)).1 ≤
        routedDepthErrorEnvelope w r m epsilon stage.1 :=
  routedDepthPathRate_le_errorEnvelope h hdegree epsilon hsmall stage.1
    (routedDepthPathStagePath m w depth path stage)
end QEC.Distillation.HH18Parameterized
