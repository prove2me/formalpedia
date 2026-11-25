-- Prove2me | solution 1 for PI.EF.norm_gaussSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:17.788744+00:00
-- url     : https://prove2.me/submissions/7be414f9-cde6-41bd-bf17-bb61af855761

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter
open scoped ZMod
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ≤ N := by
  rw [gaussSum]
  calc ‖∑ a, χ a * ZMod.stdAddChar a‖ ≤ ∑ a : ZMod N, ‖χ a * ZMod.stdAddChar a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : ZMod N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
        exact DirichletCharacter.norm_le_one χ a
    _ = N := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
end PI.EF
