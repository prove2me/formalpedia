-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPooledYield_eq_sum_div_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:49:37.549919+00:00
-- url     : https://prove2.me/submissions/895b2c41-ef41-45ed-aa40-d83fbfbfa729

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledAcceptedOutput_eq_sum

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
    (depth : Nat) :
    (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ)) /
        Fintype.card (routedDepthOutputSlots m w depth) := by
  rw [routedDepthPooledYield, NNReal.coe_div,
    routedDepthPooledAcceptedOutput_eq_sum]
  rfl
end QEC.Distillation.HH18Parameterized
