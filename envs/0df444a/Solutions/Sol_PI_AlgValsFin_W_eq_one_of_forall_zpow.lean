-- Prove2me | solution 1 for PI.AlgValsFin.W.eq_one_of_forall_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:19.026727+00:00
-- url     : https://prove2.me/submissions/d797dd73-e851-4c23-9015-a6b620e12a2d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqOneOfForallZpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_NormEqOneOfForallZpow
import Theorems.Thm_UpperTheory_Reformulated_B_Qk23_eq_one_of_forall_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AlgValsFin PI.AlgValsFin.W
namespace PI.AlgValsFin.W
theorem _root_.solution {z : ℂ} (h : ∀ k : ℤ, ‖z ^ k - 1‖ < 1) : z = 1 := by
  first | exact UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow .. | (apply UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow z h | exact @UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow z
end PI.AlgValsFin.W
