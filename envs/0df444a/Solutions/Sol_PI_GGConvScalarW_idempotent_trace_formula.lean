-- Prove2me | solution 1 for PI.GGConvScalarW.idempotent_trace_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:47.987103+00:00
-- url     : https://prove2.me/submissions/e4227503-9c64-4eb6-ab4e-35df3f24dce6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PI.GGConvScalarW
theorem _root_.solution : IdemTrace := by
  intro V _ _ _ e he
  have h : IsIdempotentElem e := he
  exact ((LinearMap.isProj_range_iff_isIdempotentElem e).2 h).trace
end PI.GGConvScalarW
