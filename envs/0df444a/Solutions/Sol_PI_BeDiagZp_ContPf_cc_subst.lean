-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.cc_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:39.904008+00:00
-- url     : https://prove2.me/submissions/16b65b5a-c68b-4267-8268-fc88db5d58ff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_pow
import Theorems.Thm_PI_BeDiagZp_ContPf_coeff_subst_eq_sum

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
theorem _root_.solution {σ : Type} (F : PowerSeries ℂ_[p]) {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (h0 : ∀ c, MvPowerSeries.constantCoeff (G c) = 0) (hG : CC G) :
    CC fun c => PowerSeries.subst (G c) F := by
  intro e
  simp only [coeff_subst_eq_sum _ (h0 _)]
  exact continuous_finsetSum _ fun d _ => by
    have h : Continuous fun c => MvPowerSeries.coeff e (G c ^ d) := cc_pow hG d e
    exact h.const_smul (PowerSeries.coeff d F)
end PI.BeDiagZp.ContPf
