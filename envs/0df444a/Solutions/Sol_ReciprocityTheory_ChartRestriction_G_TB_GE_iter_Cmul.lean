-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.iter_Cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:32.966174+00:00
-- url     : https://prove2.me/submissions/736d9762-5ae4-4e10-bacd-477949b70623

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (D : PS k 1 d → PS k 1 d) (hD : ∀ (r : k) f, D (C r * f) = C r * D f) (n : ℕ) (r : k)
    (f : PS k 1 d) : D^[n] (C r * f) = C r * D^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, hD, ih]
end ReciprocityTheory.ChartRestriction.G.TB.GE
