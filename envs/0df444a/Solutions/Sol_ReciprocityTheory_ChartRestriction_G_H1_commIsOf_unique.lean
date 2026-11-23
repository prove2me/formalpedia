-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.commIsOf_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:00.37597+00:00
-- url     : https://prove2.me/submissions/54159472-6901-4368-b0f5-9b0d5d61b9c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_val_constGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S}
    (θx θy : ThetaGrp A L k T) (c c' : Γ(T.left, ⊤)ˣ) (h : CommIsOf A L k θx θy c) (h' : CommIsOf A L k θx θy c') :
    c = c' := by
  let s : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) (toUnit T ≫ η[A])).left
  have hs : s ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  refine unit_ext fun z _ => ?_
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have e := (val_mul hJ' _ _ s).symm.trans ((val_corr hJ' h s).symm.trans ((val_corr hJ' h' s).trans (val_mul hJ' _ _ s)))
  have e' := mul_left_cancel e
  rw [val_constGen, val_constGen, hs] at e'
  exact e'
end ReciprocityTheory.ChartRestriction.G.H1
