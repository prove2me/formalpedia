-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.expS_zero_an
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:52:23.886599+00:00
-- url     : https://prove2.me/submissions/879352cb-ebf3-40bf-93b9-46f83b0817ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ComposeLinearAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ NumberField
variable {g m n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (k : Type) [CommRing k] [Algebra ℚ k] {n d : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  have ha : PowerSeries.HasSubst (0 : PS k n d) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold FB.expS
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (PowerSeries.exp k)]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, zero_mul, zero_add,
    PowerSeries.constantCoeff_exp, map_one, ← PowerSeries.coe_substAlgHom ha, map_one]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
