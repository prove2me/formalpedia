-- Prove2me | solution 1 for PI.BeDiagZp.expMv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:56.277818+00:00
-- url     : https://prove2.me/submissions/93d48c7f-ddf6-463a-88b2-06c4493496a2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_coeff_expMv_eq_expT
import Theorems.Thm_PI_BeDiagZp_coeff_expT_add

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
    (hy : constantCoeff y = 0) : expMv (x + y) = expMv x * expMv y := by
  ext α
  have hN : Finsupp.degree α < Finsupp.degree α + 1 := Nat.lt_succ_self _
  have hxy : constantCoeff (x + y) = 0 := by rw [map_add, hx, hy, add_zero]
  rw [coeff_expMv_eq_expT hxy hN, coeff_expT_add hx hy hN, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun βγ hβγ => ?_
  have hd : Finsupp.degree α = Finsupp.degree βγ.1 + Finsupp.degree βγ.2 := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hβγ]
  rw [coeff_expMv_eq_expT (N := Finsupp.degree α + 1) hx (by omega),
    coeff_expMv_eq_expT (N := Finsupp.degree α + 1) hy (by omega)]
end PI.BeDiagZp
