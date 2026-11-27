-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt.sepSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:27:28.554088+00:00
-- url     : https://prove2.me/submissions/0a936567-5eb8-4b64-8587-8c64706e6db0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_ChPt_eq_of_mod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


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
open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
theorem _root_.solution : SepSt := by
  intro T A O _ _ _ _ _ p hH h h' H
  ext z
  refine eq_of_mod p hH (h z) (h' z) fun n => ?_
  have := AlgHom.congr_fun (H n) z
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using this
end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
