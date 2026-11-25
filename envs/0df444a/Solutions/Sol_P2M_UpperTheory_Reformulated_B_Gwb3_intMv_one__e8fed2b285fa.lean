-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Gwb3_intMv_one__e8fed2b285fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:59.3819+00:00
-- url     : https://prove2.me/submissions/39845cc1-0a8c-43f9-b0d4-ee58e39ea576

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralMv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gwb3.intMv_one
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1}, UpperTheory.Reformulated.B.Gwb3.IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := by
  intro p inst σ n
  classical
  show ‖MvPowerSeries.coeff n (1 : MvPowerSeries σ ℂ_[p])‖ ≤ (1 : ℝ)
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact norm_one.le
  · rw [norm_zero]
    exact zero_le_one
end UpperTheory.Reformulated.B.Gwb3.intMv_one
