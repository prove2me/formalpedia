-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_IntegralPolynomialSecond_intMv_mul__1c3176243ba0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:17.616948+00:00
-- url     : https://prove2.me/submissions/efdfcff9-2c44-43f3-8e99-bc0fba39d389

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv (F * G) := by
  intro p _ σ F G hF hG n
  classical
  change ‖MvPowerSeries.coeff n (F * G)‖ ≤ 1
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro q _
  rw [norm_mul]
  exact mul_le_one₀ (hF q.1) (norm_nonneg _) (hG q.2)
end UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul
