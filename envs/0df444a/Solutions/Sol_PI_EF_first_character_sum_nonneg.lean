-- Prove2me | solution 1 for PI.EF.first_character_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:08.084854+00:00
-- url     : https://prove2.me/submissions/6009264c-38cb-4f6c-b7f0-6b633f05f1b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing

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
open Complex
namespace PI.EF
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 ≤ S1 χ := by
  unfold S1
  exact finsum_nonneg (fun ρ => finsum_nonneg (fun _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
end PI.EF
