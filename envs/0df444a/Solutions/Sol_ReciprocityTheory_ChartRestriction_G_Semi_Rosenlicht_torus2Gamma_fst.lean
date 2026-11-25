-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Gamma_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:39:04.596811+00:00
-- url     : https://prove2.me/submissions/fb380761-c78f-45cd-809b-99aefb1af29f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2Iso_hom_fst
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
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution (x : Γ((splitTorus (Spec (.of K)) X).left, ⊤)) :
    (torus2Gamma K X).hom
      ((fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom x) =
      (torusGamma K X).hom x ⊗ₜ 1 := by
  have e1 : (fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop ≫
      torus2Gamma K X = torusGamma K X ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) := by
    rw [torus2Gamma, torusGamma, ← Category.assoc, ← comp_appTop_lemma, torus2Iso_hom_fst,
      comp_appTop_lemma]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality]
  refine (congrArg (fun φ => φ.hom x) e1).trans ?_
  first
  | (simp; done)
  | rfl
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
