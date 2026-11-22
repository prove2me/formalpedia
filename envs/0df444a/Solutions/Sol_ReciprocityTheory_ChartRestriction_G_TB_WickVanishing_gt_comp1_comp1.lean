-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_comp1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:36.218811+00:00
-- url     : https://prove2.me/submissions/f3385fe0-1cbf-4d81-8c27-dfd9096e972f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant

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
theorem _root_.solution {n : ℕ} (f g : Pt k 1 d) (hg : GP g) (a : Pt k n d) (ha : GP a) :
    comp1 (comp1 f g) a = comp1 f (comp1 g a) := by
  funext i
  show ev ![a] (ev ![g] (f i)) = ev ![comp1 g a] (f i)
  rw [gt_ev_ev ![a] ![g] (single_point_zero_constant ha) (single_point_zero_constant hg) (f i)]
  congr 1
  funext j l
  fin_cases j
  rfl
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
