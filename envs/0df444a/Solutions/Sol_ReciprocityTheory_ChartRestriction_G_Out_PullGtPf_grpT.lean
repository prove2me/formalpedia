-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.grpT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:54.506198+00:00
-- url     : https://prove2.me/submissions/d98979ac-2318-47dc-94ab-8ba92ea354f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
open Semi Geo.Tor
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} (φ : R →+* R') (hφ : I.map φ ≤ I') (e : ℕ)
variable {φ hφ e}
variable (hφ e) {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ X)
namespace ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
theorem _root_.solution : IsGrpPullback (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X')
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X) (sE φ hφ e) (hT hφ e xe) := by
  have A := isGrpPullback_pullback (splitTorusAff ZU X') (toZ (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))))
  have B := isGrpPullback_of_iso (eψ xe)
  have C := A.comp B
  have D := isGrpPullback_pullback (splitTorusAff ZU X) (toZ (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  exact D.cancel (C.congr (specULiftZIsTerminal.hom_ext _ _) ((pullback.lift_fst _ _ _).trans
    (congrArg (pullback.fst _ _ ≫ ·) (specψ_left xe).symm)).symm) (pullback.lift_snd _ _ _)
end ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
