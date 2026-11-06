-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModuleNestedImageRestriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:05:42.329522+00:00
-- url     : https://prove2.me/submissions/ad040d77-fc3d-420b-979e-4709e6edeaf6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (M : X.Modules) (s : Γ(M, f ''ᵁ ⊤)) :
    M.presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      (M.presheaf.map (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op s) =
    M.presheaf.map (homOfLE (schemeNestedImage_le f g)).op s := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl
end QEC.Coding.AlgebraicGeometry
