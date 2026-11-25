-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.coeff_subst_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:15.64064+00:00
-- url     : https://prove2.me/submissions/e4ad1f6d-4203-4bfa-9211-c7e723e95aeb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Theorems.Thm_PI_BeDiagZp_ContPf_coeff_pow_eq_zero

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
theorem _root_.solution {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a F) =
      ∑ d ∈ Finset.range (e.degree + 1), PowerSeries.coeff d F • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hd
  simp only [coeff_pow_eq_zero a ha e d (by omega), smul_zero]
end PI.BeDiagZp.ContPf
