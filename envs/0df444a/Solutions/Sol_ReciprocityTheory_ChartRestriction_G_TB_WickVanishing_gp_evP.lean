-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_evP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:54.071936+00:00
-- url     : https://prove2.me/submissions/6e4d9b3a-e779-4f39-bf51-e0571c1af0de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev

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
theorem _root_.solution {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a : Pt k m d) (ha : GP a) :
    GP (evP V a) := by
  show ∀ i, _
  intro i
  exact gt_const_ev V hV (a i) (ha i)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
