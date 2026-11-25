-- Prove2me | solution 1 for PI.SZGW.isClosed_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:27.523867+00:00
-- url     : https://prove2.me/submissions/dbc337de-e278-4860-9bf2-f71cff2e785a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_IsClosedSimeqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.SZGW
open PI.BeDiagZp.ContPf
namespace PI.SZGW
theorem _root_.solution {p : ℕ} [Fact p.Prime] {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (hG : CC G) : IsClosed {c : ℂ_[p] | PI.BeDiagZp.IntegralMv (G c)} := by
  simp only [PI.BeDiagZp.IntegralMv, PI.BeDiagZp.IsIntP, Set.ofPred_forall]
  exact isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hG α)) continuous_const
end PI.SZGW
