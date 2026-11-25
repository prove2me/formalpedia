-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_charGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:42.034385+00:00
-- url     : https://prove2.me/submissions/cbd702ce-ca89-42b3-ac3b-b1986ea5744d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsTor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsVal

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
variable {Y Z W : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {L : LB Y} (χ : X)
    (w : W ⟶ (splitTorus S X ⊗ G).left) (z : W) (J : (W ⟶ Y) → L.ι) :
    val (charGen X G L χ) w z J = gm (w ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ) := by
  unfold val gm charGen res pullU
  have hm : w z ∈ L.wchart PEmpty.elim (fun k => J (w ≫ k.elim)) := by
    unfold LB.wchart
    simp
  rw [dif_pos hm, dif_pos (show (w ≫ (fst (splitTorus S X) G).left) z ∈
    (⊤ : (splitTorus S X).left.Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
    Scheme.Hom.comp_app, CommRingCat.comp_apply]
  erw [Function.comp_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply]
  rw [Scheme.Hom.stalkMap_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
