-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_IntegralPolynomialThird_intMv_C__365afd2ae557
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:21.145305+00:00
-- url     : https://prove2.me/submissions/6deb558c-ca26-402f-93e1-d4ce6c2355cc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialThird

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IntegralPolynomialThird.intMv_C
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {c : ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP c → UpperTheory.Reformulated.B.IntegralPolynomialThird.IntegralMv ((MvPowerSeries.C : ℂ_[p] → MvPowerSeries σ ℂ_[p]) c) := by
  intro p _ σ c hc n
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · show ‖(0 : ℂ_[p])‖ ≤ (1 : ℝ)
    rw [norm_zero]
    exact zero_le_one
end UpperTheory.Reformulated.B.IntegralPolynomialThird.intMv_C
