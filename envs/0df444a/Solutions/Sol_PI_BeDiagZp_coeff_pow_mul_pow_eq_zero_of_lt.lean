-- Prove2me | solution 1 for PI.BeDiagZp.coeff_pow_mul_pow_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:45.389961+00:00
-- url     : https://prove2.me/submissions/5049773a-ba20-4fb6-a78f-ebb9723483fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt

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
    (hy : constantCoeff y = 0) {m j : ℕ} {α : σ →₀ ℕ} (h : Finsupp.degree α < m + j) :
    coeff α (x ^ m * y ^ j) = 0 := by
  apply coeff_of_lt_order
  calc ((Finsupp.degree α : ℕ) : ℕ∞) < ((m + j : ℕ) : ℕ∞) := by exact_mod_cast h
    _ = (m : ℕ∞) + (j : ℕ∞) := by push_cast; rfl
    _ ≤ (x ^ m).order + (y ^ j).order :=
        add_le_add (le_order_pow_of_constantCoeff_eq_zero m hx)
          (le_order_pow_of_constantCoeff_eq_zero j hy)
    _ ≤ (x ^ m * y ^ j).order := le_order_mul
end PI.BeDiagZp
