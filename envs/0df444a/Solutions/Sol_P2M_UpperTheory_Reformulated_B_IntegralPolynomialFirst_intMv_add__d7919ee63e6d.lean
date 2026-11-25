-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_IntegralPolynomialFirst_intMv_add__d7919ee63e6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:40.54582+00:00
-- url     : https://prove2.me/submissions/9b5d3903-60a7-4f82-85cf-81eb3d6e00f2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IntegralPolynomialFirst.intMv_add
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv (F + G) := by
  intro p _ σ F G hF hG n
  have h1 : ‖MvPowerSeries.coeff n F‖ ≤ (1 : ℝ) := hF n
  have h2 : ‖MvPowerSeries.coeff n G‖ ≤ (1 : ℝ) := hG n
  show ‖MvPowerSeries.coeff n (F + G)‖ ≤ (1 : ℝ)
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
end UpperTheory.Reformulated.B.IntegralPolynomialFirst.intMv_add
