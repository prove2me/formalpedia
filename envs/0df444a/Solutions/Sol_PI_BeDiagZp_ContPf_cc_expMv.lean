-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.cc_expMv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:57.76685+00:00
-- url     : https://prove2.me/submissions/95bbf558-5da7-4518-bb38-0489ef8a6142

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
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
open PI PI.BeDiagZp PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.ContPf
theorem _root_.solution {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hG : CC G) :
    CC fun c => expMv (G c) := by
  intro e
  show Continuous fun c => ∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (G c ^ n) / (n.factorial : ℂ_[p])
  exact continuous_finsetSum _ fun n _ => (cc_pow hG n e).div_const _
end PI.BeDiagZp.ContPf
