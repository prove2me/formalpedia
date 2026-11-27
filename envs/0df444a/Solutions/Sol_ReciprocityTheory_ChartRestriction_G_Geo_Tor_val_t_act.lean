-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_t_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:30:36.46744+00:00
-- url     : https://prove2.me/submissions/e384618d-3430-4bac-a575-91a4a477a1eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsTor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_charGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (χ : D.X) {W : Scheme.{0}} (w : W ⟶ (WeightPf.Te D I e ⊗ thickObj R I e G).left) (z : W)
    {J : (W ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (g.t χ) (w ≫ (WeightPf.act g).left) z J =
      gm (w ≫ (fst (WeightPf.Te D I e) (thickObj R I e G)).left) z ⊤ (charUnit _ D.X χ) *
        val (g.t χ) (w ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left) z J := by
  have hc := val_corr hJ (g.t_weight χ) w
  rw [val_pull, val_mul, val_pull, val_charGen] at hc
  · exact hc
  all_goals exact hJ
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
