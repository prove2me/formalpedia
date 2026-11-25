-- Prove2me | solution 1 for P2M_PI_OneCosetSharp_W_P2_allow_lt___8cf0e0a7f824
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:04.049555+00:00
-- url     : https://prove2.me/submissions/d24ed1ea-feac-4a59-882c-138383fd66ee

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
theorem _root_.solution {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : φ k₀ m p < φ k₀ m q := by
  unfold Allow at h
  unfold φ
  split_ifs at h ⊢ <;> omega
end PI.OneCosetSharp.W.P2
