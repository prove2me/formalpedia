-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.good_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:12.273731+00:00
-- url     : https://prove2.me/submissions/cec79bc6-2ccf-4d6c-b906-73842c3ae1ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (E0 : AA k d) (T : Module.End k (AA k d)) (hT : ∀ X, GoodE R E0 X → GoodE R E0 (T X))
    (n : ℕ) : ∀ X, GoodE R E0 X → GoodE R E0 ((T ^ n) X) := by
  induction n with
  | zero =>
    intro X hX
    rw [pow_zero]
    exact hX
  | succ n ih =>
    intro X hX
    rw [pow_succ]
    exact ih (T X) (hT X hX)
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
