-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.specMap_appLE_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:10.600975+00:00
-- url     : https://prove2.me/submissions/a3a71386-6745-4224-87b2-8f8b95411b20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
variable {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S)
variable {X Y} {V : Y.left.Opens} (hV : IsAffineOpen V)
attribute [local instance] zuAlg
namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
theorem _root_.solution {R R' : CommRingCat.{0}} (f : R ⟶ R') (e) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso R').hom = f := by
  have h1 : (Spec.map f).appLE ⊤ ⊤ e = (Spec.map f).appTop := by
    first
    | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl)
    | (simp only [Scheme.Hom.appLE]
       erw [show (homOfLE e).op = 𝟙 (Opposite.op (⊤ : (Spec R').Opens)) from Subsingleton.elim _ _,
         CategoryTheory.Functor.map_id, Category.comp_id]
       rfl)
  rw [h1, Scheme.ΓSpecIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
