-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.evP_addOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:28.337229+00:00
-- url     : https://prove2.me/submissions/de7c93fd-80d4-405c-9a70-26f06c4a6192

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant

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
theorem _root_.solution {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (F : Fin d → PS k 2 d)
    (a b : Pt k m d) (ha : GP a) (hb : GP b) : evP V (addOf F a b) = addOf F (evP V a) (evP V b) := by
  funext i
  show ev V (ev ![a, b] (F i)) = ev ![evP V a, evP V b] (F i)
  rw [gt_ev_ev V ![a, b] hV (pair_points_zero_constant ha hb) (F i)]
  congr 1
  funext j l
  fin_cases j <;> rfl
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
