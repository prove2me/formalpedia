-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.isRQ_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:15.321572+00:00
-- url     : https://prove2.me/submissions/589458c9-5778-43f3-be6c-2826c5eddf11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution : IsRQ (R := ℤ) ℚ := by
  unfold IsRQ
  refine ⟨(algebraMap ℤ ℚ).injective_int, fun y => ⟨y.num, y.den, Nat.pos_of_ne_zero y.den_nz, ?_⟩⟩
  rw [eq_intCast]
  exact Rat.den_mul_eq_num y
end ReciprocityTheory.ChartRestriction.G.TB
