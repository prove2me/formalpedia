-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.S_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:10.781125+00:00
-- url     : https://prove2.me/submissions/91fc6807-4566-4278-86fc-a8ef4f513101

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
theorem _root_.solution {k₀ m t N p q s : ℕ} (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q s) : S k₀ m t N p s := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  by_cases hps : p = s
  · exact Or.inl hps
  right
  unfold Allow at h1 h2 ⊢
  generalize (p - (k₀ + m - 1)) / t = bp at *
  generalize (q - (k₀ + m - 1)) / t = bq at *
  generalize (s - (k₀ + m - 1)) / t = bs at *
  split_ifs at h1 h2 ⊢ <;> omega
end PI.OneCosetSharp.W.P2
