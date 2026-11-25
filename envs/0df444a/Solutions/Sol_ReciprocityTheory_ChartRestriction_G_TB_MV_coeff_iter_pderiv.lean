-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_iter_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:43.278223+00:00
-- url     : https://prove2.me/submissions/efedf48b-eb78-42be-a771-64ad73940795

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.MV
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.MV
theorem _root_.solution (i : σ) (c : ℕ) (g : MvPowerSeries σ k) (n : σ →₀ ℕ) :
    coeff n ((pderiv k i)^[c] g) =
      coeff (n + c • Finsupp.single i 1) g * ((n i + 1).ascFactorial c : k) := by
  induction c generalizing n g with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv]
    have h1 : n + c • Finsupp.single i 1 + Finsupp.single i 1 = n + (c + 1) • Finsupp.single i 1 := by
      rw [add_smul, one_smul, add_assoc]
    have h2 : ((n + c • Finsupp.single i 1 : σ →₀ ℕ)) i = n i + c := by simp
    rw [h1, h2, Nat.ascFactorial_succ]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.TB.MV
