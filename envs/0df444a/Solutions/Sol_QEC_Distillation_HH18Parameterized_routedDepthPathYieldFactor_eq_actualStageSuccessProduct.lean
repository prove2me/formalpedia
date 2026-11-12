-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_eq_actualStageSuccessProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:49:19.209522+00:00
-- url     : https://prove2.me/submissions/c8be053d-ef2b-4460-ae8d-41629b19f8fa

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageYield_eq_actualRunSuccess

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
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) =
      ∏ stage : Fin depth,
        (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by
  classical
  rw [routedDepthPathYieldFactor, NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro stage _
  exact routedDepthPathStageYield_eq_actualRunSuccess
    h hdegree epsilon hsmall depth path stage
end QEC.Distillation.HH18Parameterized
