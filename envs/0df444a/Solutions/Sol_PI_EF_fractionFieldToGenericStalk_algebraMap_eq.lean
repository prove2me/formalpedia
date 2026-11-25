-- Prove2me | solution 1 for PI.EF.fractionFieldToGenericStalk_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:12.403607+00:00
-- url     : https://prove2.me/submissions/09072db2-7569-4ff9-b861-949721d4f547

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
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : ℝ) :
    psi0 χ u = psiRaw χ u - del1 χ * u := by
  unfold psi0 psiRaw del1
  split_ifs <;> simp
end PI.EF
