-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.allow_col_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:23.26758+00:00
-- url     : https://prove2.me/submissions/4defda18-fedd-4ffb-8c94-4372c76d413d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.P2
namespace PI.OneCosetSharp.W.P2
theorem _root_.solution {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : p < k₀ + m - 1 := by
  unfold Allow at h
  split_ifs at h <;> omega
end PI.OneCosetSharp.W.P2
