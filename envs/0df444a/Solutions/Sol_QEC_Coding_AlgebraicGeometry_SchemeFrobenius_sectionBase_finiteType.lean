-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.sectionBase_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:03.999206+00:00
-- url     : https://prove2.me/submissions/ef567417-8522-4478-b6c0-b755a9814d2f

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
theorem _root_.solution [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) : (sectionBase p X f U).FiniteType := by
  have hbase := f.finiteType_appLE (isAffineOpen_top _) hU (show U ≤ f ⁻¹ᵁ ⊤ from le_top)
  have hiso : (Scheme.ΓSpecIso (.of (ZMod p))).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ZMod p))).inv).surjective
  exact hbase.comp hiso
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
