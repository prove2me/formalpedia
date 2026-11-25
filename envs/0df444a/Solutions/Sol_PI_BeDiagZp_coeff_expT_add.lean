-- Prove2me | solution 1 for PI.BeDiagZp.coeff_expT_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:33.065204+00:00
-- url     : https://prove2.me/submissions/f4161209-b774-4376-bd9b-56200c044113

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_coeff_pow_mul_pow_eq_zero_of_lt
import Theorems.Thm_PI_BeDiagZp_expT_add
import Theorems.Thm_PI_BeDiagZp_expT_mul_expT

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
open PI PI.BeDiagZp
open MvPowerSeries
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp
theorem _root_.solution {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {α : σ →₀ ℕ} {N : ℕ} (hN : Finsupp.degree α < N) :
    coeff α (expT (x + y) N) = coeff α (expT x N * expT y N) := by
  rw [expT_add, expT_mul_expT, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_sum, map_sum]
  apply Finset.sum_subset
  · intro j hj; simp only [Finset.mem_range] at *; omega
  · intro j _ hj
    simp only [Finset.mem_range, not_lt] at hm hj
    rw [map_smul, coeff_pow_mul_pow_eq_zero_of_lt hx hy (by omega), smul_zero]
end PI.BeDiagZp
