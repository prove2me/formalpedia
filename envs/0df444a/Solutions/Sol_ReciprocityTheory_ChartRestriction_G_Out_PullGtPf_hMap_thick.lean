-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.hMap_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:28:20.795578+00:00
-- url     : https://prove2.me/submissions/5cde7f22-949e-47e9-8c27-5d4595cdfb7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_sE_trans

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
namespace ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
theorem _root_.solution (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    thickMap R' I' e Y' ≫ hMap (hφ := hφ) (e := e + 1) Y Y' b =
      hMap (hφ := hφ) (e := e) Y Y' b ≫ thickMap R I e Y := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hMap_fst]
    simp only [thickMap, pullback.map]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
    simp only [Category.comp_id, Category.id_comp]
    rw [hMap_fst]
  · rw [Category.assoc, Category.assoc, hMap_snd]
    simp only [thickMap, pullback.map]
    erw [pullback.lift_snd_assoc, pullback.lift_snd]
    simp only [Category.assoc, sE_trans]
    simp only [← Category.assoc]
    rw [hMap_snd]
end ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
