-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_IntegralMvPowerSeriesOverPadicComplex_intMv_zero__d421439abc26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:05.336528+00:00
-- url     : https://prove2.me/submissions/25f5c0b8-c675-4cc7-bf80-4d8b0ac0c4c5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialSixth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.intMv_zero
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1}, UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := by
  intro p inst σ n
  show ‖(MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) 0‖ ≤ (1 : ℝ)
  rw [map_zero, norm_zero]
  exact zero_le_one
end UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.intMv_zero
