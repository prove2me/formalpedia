-- Prove2me | solution 1 for PI.SZGW.isClosed_simeq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:40.708875+00:00
-- url     : https://prove2.me/submissions/24ad345b-cc78-4127-8de0-4cefb5b5642c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_IsClosedSimeqZero
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_const
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_expMv
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_sub


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
    (hG : CC G) : IsClosed {c : ℂ_[p] | PI.BeDiagZp.Simeq (G c) 0} := by
  have hF : CC fun c => G c - 0 := cc_sub hG (cc_const 0)
  have hE := cc_expMv hF
  simp only [PI.BeDiagZp.Simeq, PI.BeDiagZp.IntegralMv, PI.BeDiagZp.IsIntP, Set.ofPred_and,
    Set.ofPred_forall]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const)
    (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)
  exact (hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _
end PI.SZGW
