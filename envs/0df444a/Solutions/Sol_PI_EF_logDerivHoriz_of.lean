-- Prove2me | solution 1 for PI.EF.logDerivHoriz_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:30.938616+00:00
-- url     : https://prove2.me/submissions/dadc368c-89e5-4ddf-80a6-9dc6d1f1f5b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds
import Theorems.Thm_PI_EF_norm_logDeriv_horiz

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
namespace PI.EF
theorem _root_.solution {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) :
    LogDerivHoriz κ (4 * Cl + 2 * Cw * κ + 16) := by
  unfold PI.EF.LogDerivHoriz
  intro N _ χ hχ T' hT' hg σ h1 h2
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  constructor
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])
end PI.EF
