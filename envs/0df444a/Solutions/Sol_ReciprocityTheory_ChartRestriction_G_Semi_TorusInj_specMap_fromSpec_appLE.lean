-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.specMap_fromSpec_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:42.33646+00:00
-- url     : https://prove2.me/submissions/c786f1d7-3107-4935-af2c-07941660ca72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_specMap_appLE_top

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
theorem _root_.solution {R : CommRingCat.{0}} (f : Γ(Y.left, V) ⟶ R) (e) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom = f := by
  have h1 : (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e =
      hV.fromSpec.appLE V ⊤ (by simp) ≫ (Spec.map f).appLE ⊤ ⊤ (by simp) :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : hV.fromSpec.appLE V ⊤ (by simp) = (Scheme.ΓSpecIso Γ(Y.left, V)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    conv_rhs => rw [← Category.comp_id (Scheme.ΓSpecIso Γ(Y.left, V)).inv]
    congr 1
  rw [h1, h2, Category.assoc]
  exact specMap_appLE_top f _
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
