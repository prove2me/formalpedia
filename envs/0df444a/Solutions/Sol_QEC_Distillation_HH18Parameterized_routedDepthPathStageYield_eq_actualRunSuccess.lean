-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathStageYield_eq_actualRunSuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:45:20.649009+00:00
-- url     : https://prove2.me/submissions/e47a5264-0938-4efa-b66c-752f48ab664d

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield

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
    (routedDepthPathStageYield h hdegree epsilon hsmall depth path stage : ℝ) =
      (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability :=
  rfl
end QEC.Distillation.HH18Parameterized
