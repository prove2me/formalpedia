-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:56.010021+00:00
-- url     : https://prove2.me/submissions/a0cf0ffa-1657-4b6d-9b1e-896694016115

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nabla_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u u' φ φ' : Fin d → k) :
    nablaL B h m (u + u') (φ + φ') = nablaL B h m u φ + nablaL B h m u' φ' := LinearMap.ext fun G => by
    simp only [LinearMap.add_apply, nablaL_apply]
    exact nabla_add B h m u u' φ φ' G
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
