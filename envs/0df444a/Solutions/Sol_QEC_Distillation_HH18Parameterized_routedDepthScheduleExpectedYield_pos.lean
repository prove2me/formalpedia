-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleExpectedYield_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:23:15.324925+00:00
-- url     : https://prove2.me/submissions/79a508b5-3455-44dc-a249-63783dc72cd4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_pos


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
    0 < (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) :=
  routedDepthPooledYield_pos h hdegree epsilon hsmall depth
end QEC.Distillation.HH18Parameterized
