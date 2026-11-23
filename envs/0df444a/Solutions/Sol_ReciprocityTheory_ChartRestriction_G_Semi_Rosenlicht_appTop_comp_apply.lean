-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.appTop_comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:12.289416+00:00
-- url     : https://prove2.me/submissions/5217a13a-a6e5-4c32-b745-ea85963036fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
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
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := by
  rw [comp_appTop_lemma]
  rfl
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
