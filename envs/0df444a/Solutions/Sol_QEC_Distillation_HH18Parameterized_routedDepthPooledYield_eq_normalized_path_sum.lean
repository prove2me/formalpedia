-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPooledYield_eq_normalized_path_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:58:26.516601+00:00
-- url     : https://prove2.me/submissions/1b6ebd4d-325e-4edf-9480-f04c15ce4d32

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathTypedOutputSlots_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_eq_sum_div_card

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
        (logicalOutputCount m w : ℝ) ^ depth := by
  rw [routedDepthPooledYield_eq_sum_div_card,
    routedDepthPathTypedOutputSlots_card]
  norm_cast
end QEC.Distillation.HH18Parameterized
