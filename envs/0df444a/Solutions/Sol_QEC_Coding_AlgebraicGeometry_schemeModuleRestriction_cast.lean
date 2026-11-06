-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModuleRestriction_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:04:39.710581+00:00
-- url     : https://prove2.me/submissions/a85536db-1f5f-4950-91a3-5e28a74eed80

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
theorem _root_.solution (M : X.Modules) {W V U : X.Opens}
    (e : W = V) (h : V ≤ U) (s : Γ(M, U)) :
    M.presheaf.map (eqToHom e).op (M.presheaf.map (homOfLE h).op s) =
      M.presheaf.map (homOfLE (e.le.trans h)).op s := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl
end QEC.Coding.AlgebraicGeometry
