-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_IntegralPolynomialFourth_intMv_neg__ae9784f0616c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:09.173991+00:00
-- url     : https://prove2.me/submissions/f54b9b53-1346-4745-b2bb-fa757f40c5f8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFourth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IntegralPolynomialFourth.intMv_neg
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv (-F) := by
  intro p _ σ F h n
  have hn : ‖MvPowerSeries.coeff n F‖ ≤ (1 : ℝ) := h n
  show ‖MvPowerSeries.coeff n (-F)‖ ≤ (1 : ℝ)
  rw [map_neg, norm_neg]
  exact hn
end UpperTheory.Reformulated.B.IntegralPolynomialFourth.intMv_neg
