-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.S_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:06.940334+00:00
-- url     : https://prove2.me/submissions/49cb9343-19c9-4796-8a55-32bd9ed170e8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt
import Theorems.Thm_PI_OneCosetSharp_W_P2_allow_col_lt
import Theorems.Thm_P2M_PI_OneCosetSharp_W_P2_allow_lt___8cf0e0a7f824

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
theorem _root_.solution {k₀ m t N p q : ℕ} (hp : p < k₀ + m - 1) (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q p) : p = q := by
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  · exact h2.symm
  have hq := allow_col_lt hp h2
  have a := allow_lt_φ hq h1
  have b := allow_lt_φ hp h2
  omega
end PI.OneCosetSharp.W.P2
