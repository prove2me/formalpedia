-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.schwarzLemmaBall_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:16.480007+00:00
-- url     : https://prove2.me/submissions/22739d9e-78d3-49cd-9841-f702702dcd0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SchwarzLemmaBallHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_exp_nine_quarters_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Metric Set
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : SchwarzLemmaBall := by
  intro V _ _ γ ρ S hρ hd hb h1 h2 Z hZ
  have hS : 0 < S := by linarith [norm_nonneg (γ 0)]
  have hmaps : MapsTo γ (ball 0 ρ) (closedBall (γ 0) ((Real.exp (9 / 4) + 1) * S)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖γ z - γ 0‖ ≤ ‖γ z‖ + ‖γ 0‖ := norm_sub_le _ _
      _ ≤ Real.exp (9 / 4) * S + S := add_le_add (hb z (ball_subset_closedBall hz)) h2
      _ = (Real.exp (9 / 4) + 1) * S := by ring
  have hZρ : Z ∈ ball (0 : V) ρ := ball_subset_ball (by linarith) hZ
  have key := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hd.mono ball_subset_closedBall) hmaps hZρ
  have hZn : ‖Z‖ < ρ / 21 := by simpa using hZ
  rw [dist_zero_right] at key
  intro h0
  rw [h0, dist_comm, dist_zero_right] at key
  have hexp := exp_nine_quarters_lt
  have : (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ < S / 2 := by
    calc (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ ≤ (Real.exp (9 / 4) + 1) * S / ρ * (ρ / 21) := by
          gcongr
      _ = (Real.exp (9 / 4) + 1) * S / 21 := by field_simp
      _ < S / 2 := by nlinarith
  linarith
end ReciprocityTheory.ChartRestriction.G.FD
