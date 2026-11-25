-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.coord_id_torusGamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:00.208337+00:00
-- url     : https://prove2.me/submissions/2677ffcd-4b35-4828-a42d-80118188bd4f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusIso_hom_fst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
namespace ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
namespace Rosenlicht
private theorem comp_appTop_lemma {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop := by
  first
  | rfl
  | (simp; done)
  | exact Scheme.Hom.comp_appTop f g
section
variable {S : Scheme.{u}}
end
section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra
end
section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
end
section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
end
end Rosenlicht
end ReciprocityTheory.ChartRestriction.G.Semi
end

set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution :
    coord (𝟙 (splitTorus (Spec (.of K)) X)) ≫ torusGamma K X =
      CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X)) := by
  have key : (torusFst (Spec (.of K)) X).appTop ≫ (torusIso K X).hom.appTop =
      ((torusIso K X).hom ≫ torusFst (Spec (.of K)) X).appTop := (comp_appTop_lemma _ _).symm
  show (Scheme.ΓSpecIso _).inv ≫ (𝟙 _ ≫ torusFst (Spec (.of K)) X).appTop ≫
    (torusIso K X).hom.appTop ≫ (Scheme.ΓSpecIso _).hom = _
  rw [Category.id_comp, ← Category.assoc (torusFst (Spec (.of K)) X).appTop, key, torusIso_hom_fst,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
