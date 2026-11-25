-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.ev_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:35.736203+00:00
-- url     : https://prove2.me/submissions/5fbd5202-5a0d-4784-9974-cf3a9335a6b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_pt_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_specMap_appLE_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_charUnit_val

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
theorem _root_.solution (χ : X) :
    ev hV (((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ)) =
      AddMonoidAlgebra.single χ 1 := by
  have hfst : (pt hV ≫ (fst (splitTorus S X) Y).left) ≫ tFst (S := S) X =
      ptZ (X := X) (V := V) := by
    rw [pt_fst]; exact pullback.lift_fst _ _ _
  have key : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫
      ((tFst (S := S) X).appLE ⊤ ⊤ (tle _) ≫
      ((fst (splitTorus S X) Y).left.appTop ≫
      ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op ≫
      ((pt hV).appLE _ ⊤ (pt_le hV) ≫ (Scheme.ΓSpecIso (GA (X := X) (V := V))).hom)))) =
      CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra Γ(Y.left, V) X)) := by
    have hT : (fst (splitTorus S X) Y).left.appTop = (fst (splitTorus S X) Y).left.appLE ⊤ ⊤ (tle _) := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [hT, ← Category.assoc ((splitTorus S X ⊗ Y).left.presheaf.map _), Scheme.Hom.map_appLE,
      ← Category.assoc ((fst (splitTorus S X) Y).left.appLE _ _ _), Scheme.Hom.appLE_comp_appLE,
      ← Category.assoc ((tFst (S := S) X).appLE ⊤ ⊤ _),
      Scheme.Hom.appLE_comp_appLE, appLE_of_eq hfst]
    exact specMap_appLE_top _ _
  have := congrArg (fun φ => φ.hom (AddMonoidAlgebra.single χ (1 : ULift.{0} ℤ))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [ev, RingHom.comp_apply, chiP, charUnit_val]
  convert this using 1
  simp [AddMonoidAlgebra.algebraMap_def]
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
