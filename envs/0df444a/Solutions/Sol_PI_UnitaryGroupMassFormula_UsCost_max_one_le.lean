-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.max_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:38.897953+00:00
-- url     : https://prove2.me/submissions/c25f6739-1847-4914-b47a-792fa5fabd86

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (c t : ℝ) (ht : 1 ≤ t) (x : ℝ) (hx : x ≤ c * t) : max 1 x ≤ (1 + |c|) * t := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0
  have h2 : 0 ≤ |c| * t := mul_nonneg (abs_nonneg c) ht0
  refine max_le ?_ ?_ <;> nlinarith
end PI.UnitaryGroupMassFormula.UsCost
