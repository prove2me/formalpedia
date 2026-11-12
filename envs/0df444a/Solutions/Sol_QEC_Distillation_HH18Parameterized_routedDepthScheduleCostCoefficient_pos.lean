-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleCostCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:53:18.747291+00:00
-- url     : https://prove2.me/submissions/e023ed89-74db-495e-aa5a-ffba3eb562ac

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleLogGrowthBase_pos

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
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    0 < routedDepthScheduleCostCoefficient h epsilon := by
  unfold routedDepthScheduleCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (routedDepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall) _)
end QEC.Distillation.HH18Parameterized
