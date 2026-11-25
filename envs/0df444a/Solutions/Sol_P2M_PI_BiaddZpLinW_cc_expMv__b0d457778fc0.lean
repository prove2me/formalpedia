-- Prove2me | solution 1 for P2M_PI_BiaddZpLinW_cc_expMv__b0d457778fc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:50.978562+00:00
-- url     : https://prove2.me/submissions/a8c677ce-c76b-4157-9313-6cf31504129b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_BiadditiveContinuousPadic
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_pow


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
open PI PI.BiaddZpLinW
open PI.BiaddZpLin PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]
namespace PI.BiaddZpLinW
theorem _root_.solution {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hG : CC G) :
    CC fun c => expMv (G c) := by
  intro e
  show Continuous fun c => ∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (G c ^ n) / (n.factorial : ℂ_[p])
  exact continuous_finsetSum _ fun n _ => (cc_pow hG n e).div_const _
end PI.BiaddZpLinW
