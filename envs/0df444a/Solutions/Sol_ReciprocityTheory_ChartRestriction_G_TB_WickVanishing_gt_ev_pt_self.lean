-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_pt_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:13.444022+00:00
-- url     : https://prove2.me/submissions/c8a7e57a-1708-4219-80a8-25b839910e3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (f : PS k 1 d) : ev ![pt k (n := 1) d 0] f = f := by
  have h : (fun p : Fin 1 × Fin d => (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) p.1 p.2) =
      MvPowerSeries.X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    rfl
  show MvPowerSeries.subst _ f = f
  first
    | (rw [h, MvPowerSeries.subst_self]; rfl)
    | rw [h, MvPowerSeries.subst_self]
    | simp [h, MvPowerSeries.subst_self]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
