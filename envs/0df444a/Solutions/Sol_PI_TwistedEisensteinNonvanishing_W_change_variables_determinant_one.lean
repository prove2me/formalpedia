-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.change_variables_determinant_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:28.906584+00:00
-- url     : https://prove2.me/submissions/1af38cec-d925-418b-9f8e-749f7044c7f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_aff
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (hN : NTAll) : ChangeVariablesDeterminantOne := by
  intro E K _ _ _ P hp hq hK ι _ _ L τ h1 a b
  obtain ⟨a', b', h⟩ := qt_aff hN hp hq hK L τ a b
  refine ⟨a', b', fun H hH => ?_⟩
  obtain ⟨g, e⟩ := h H hH
  refine ⟨g, ?_⟩
  rw [e, h1, vq_one, zpow_zero, one_mul]
  all_goals assumption
end PI.TwistedEisensteinNonvanishing.W
