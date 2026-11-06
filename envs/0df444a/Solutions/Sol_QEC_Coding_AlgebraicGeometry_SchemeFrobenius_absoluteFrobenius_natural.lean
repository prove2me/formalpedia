-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_natural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:56:47.571563+00:00
-- url     : https://prove2.me/submissions/30308497-889f-45c5-a910-9fcb83564a85

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius

set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))
namespace QEC.Coding.AlgebraicGeometry.SchemeFrobenius
theorem _root_.solution {Y : Scheme} (g : X ⟶ Y)
    (h : Y ⟶ Spec (.of (ZMod p))) :
    absoluteFrobenius p X f ≫ g = g ≫ absoluteFrobenius p Y h := by
  have hb : (absoluteFrobenius p X f ≫ g).base = (g ≫ absoluteFrobenius p Y h).base := by
    exact (Category.id_comp g.base).trans (Category.comp_id g.base).symm
  apply Scheme.Hom.ext hb
  intro U
  have hi : (eqToHom (congrArg (fun b => (Opens.map b).obj U) hb.symm)).op =
      𝟙 (op (g ⁻¹ᵁ U)) := Subsingleton.elim _ _
  have hm : X.presheaf.map (eqToHom (congrArg (fun b => (Opens.map b).obj U) hb.symm)).op =
      𝟙 Γ(X, g ⁻¹ᵁ U) :=
    (congrArg (fun i => X.presheaf.map i) hi).trans (X.presheaf.map_id (op (g ⁻¹ᵁ U)))
  have hp2 : g.app U ≫ (absoluteFrobenius p X f).app (g ⁻¹ᵁ U) =
      (absoluteFrobenius p Y h).app U ≫ g.app U := by
    ext s
    change (g.app U s)^p = g.app U (s^p)
    exact ((g.app U).hom.map_pow s p).symm
  have hp : (absoluteFrobenius p X f ≫ g).app U = (g ≫ absoluteFrobenius p Y h).app U :=
    (Scheme.Hom.comp_app (absoluteFrobenius p X f) g U).trans
      (hp2.trans (Scheme.Hom.comp_app g (absoluteFrobenius p Y h) U).symm)
  exact (congrArg (fun r => (absoluteFrobenius p X f ≫ g).app U ≫ r) hm).trans
    ((Category.comp_id _).trans hp)
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
