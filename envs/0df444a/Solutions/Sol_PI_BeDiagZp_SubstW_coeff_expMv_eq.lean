-- Prove2me | solution 1 for PI.BeDiagZp.SubstW.coeff_expMv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:19.369794+00:00
-- url     : https://prove2.me/submissions/e372c2d9-7911-4197-b63f-01d0b45a5b62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
import Theorems.Thm_PI_BeDiagZp_SubstW_deg_eq
import Theorems.Thm_PI_BeDiagZp_SubstW_coeff_pow_eq_zero

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
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.SubstW
theorem _root_.solution {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) (d : σ →₀ ℕ) {N : ℕ} (hN : d.degree < N) :
    MvPowerSeries.coeff d (expMv F) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by
  have e1 : MvPowerSeries.coeff d (expMv F) = ∑ n ∈ Finset.range ((d.sum fun _ k => k) + 1),
      MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := rfl
  rw [e1, deg_eq]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at *
    omega
  · intro n hn hn'
    simp only [Finset.mem_range, not_lt] at hn hn'
    rw [coeff_pow_eq_zero hF (by omega), zero_div]
end PI.BeDiagZp.SubstW
