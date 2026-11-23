-- Prove2me | solution 1 for P2M_GlobalTheory_FormalLog_ev_zero__96b7e70e62c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:52.821906+00:00
-- url     : https://prove2.me/submissions/c5a2a5e7-bcd6-47f6-a628-3a4d9128c1c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_FormalLog_evHom_apply

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
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d m n : ℕ}
namespace GlobalTheory.FormalLog
theorem _root_.solution {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  simp only [← evHom_apply ha, map_zero]
end GlobalTheory.FormalLog
