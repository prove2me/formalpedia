-- Prove2me | solution 1 for P2M_GlobalTheory_Jets_map_pderiv__1dd9b2916977
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:53:46.784447+00:00
-- url     : https://prove2.me/submissions/8bcc3dff-cbb3-42fb-bf1e-36c8c9ba621c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets
namespace GlobalTheory.Jets
theorem _root_.solution {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  classical
  ext n
  simp [coeff_pderiv]
end GlobalTheory.Jets
