-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Gwb7_intMv_pderiv__f99441b0868b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:02.103693+00:00
-- url     : https://prove2.me/submissions/ea391de6-5aab-47d6-b943-2cc94374252b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntMvPderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gwb7.intMv_pderiv
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]} (i : σ),
      UpperTheory.Reformulated.B.Gwb7.IntegralMv F →
        UpperTheory.Reformulated.B.Gwb7.IntegralMv ((MvPowerSeries.pderiv ℂ_[p] i : MvPowerSeries σ ℂ_[p] → MvPowerSeries σ ℂ_[p]) F) := by
  intro p _ σ F i hF n
  have h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1 := hF _
  have h2 : ‖((n i : ℕ) : ℂ_[p]) + 1‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n i + 1)
    rwa [Nat.cast_add, Nat.cast_one] at h
  change ‖MvPowerSeries.coeff n (MvPowerSeries.pderiv ℂ_[p] i F)‖ ≤ 1
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2
end UpperTheory.Reformulated.B.Gwb7.intMv_pderiv
