-- Prove2me | solution 1 for P2M_GlobalTheory_ChartCmp_GaugeDiff_jeq_of_sub__dd57f7a2ce20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:09:23.406963+00:00
-- url     : https://prove2.me/submissions/4d0d93a9-c29f-48cc-95b7-ddee0692471a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_jeq_of_sub

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.GaugeDiff
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartCmp.GaugeDiff
theorem _root_.solution {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = g - f) :
    JEq m u v :=
  jeq_of_sub (f := g) (g := f) (fun x hx => (h x hx).symm) e
end GlobalTheory.ChartCmp.GaugeDiff
