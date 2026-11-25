-- Prove2me | solution 1 for P2M_GlobalTheory_JetSer_IntTrans_constantCoeff_map_eq_zero__741a16259184
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:08.021106+00:00
-- url     : https://prove2.me/submissions/980abc7a-8ba7-4a14-ade7-5b6ad1309304

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution {n : ℕ} {a : Pt R n d} (ha : GP a) : GP (mP f a) := fun i => by
  simp only [mP, constantCoeff_map, ha i, map_zero]
end GlobalTheory.JetSer.IntTrans
