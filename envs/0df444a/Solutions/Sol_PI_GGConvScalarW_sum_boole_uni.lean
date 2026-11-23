-- Prove2me | solution 1 for PI.GGConvScalarW.sum_boole_uni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:41.261448+00:00
-- url     : https://prove2.me/submissions/543fd4a8-bd0a-4c47-a1d7-1ba9720220d3

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
theorem _root_.solution : (∑ x : GL (Fin k) F, if IsUni k x then (1 : ℂ) else 0) = (cardU F k : ℂ) := by
  rw [Finset.sum_boole]
  unfold cardU
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
end PI.GGConvScalarW
