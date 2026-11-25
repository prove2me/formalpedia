-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.ev_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:38:03.864728+00:00
-- url     : https://prove2.me/submissions/3a3f5748-b11c-4026-a467-da41bf0fc936

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_specMap_fromSpec_appLE

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
theorem _root_.solution (h : Γ(Y.left, V)) :
    ev hV (((snd (splitTorus S X) Y).left.app V).hom h) = AddMonoidAlgebra.single 0 h := by
  have e1 : (snd (splitTorus S X) Y).left.app V ≫ (pt hV).appLE _ ⊤ (pt_le hV) ≫
      (Scheme.ΓSpecIso (GA (X := X) (V := V))).hom =
      CommRingCat.ofHom (algebraMap Γ(Y.left, V) (AddMonoidAlgebra Γ(Y.left, V) X)) := by
    rw [Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE,
      appLE_of_eq (pt_snd hV)]
    exact specMap_fromSpec_appLE hV _ _
  have := congrArg (fun φ => φ.hom h) e1
  rw [ev, RingHom.comp_apply]; simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this; convert this using 1
  simp [AddMonoidAlgebra.coe_algebraMap]
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
