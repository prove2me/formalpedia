-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_primeSpec_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:56:51.305537+00:00
-- url     : https://prove2.me/submissions/08989cf1-cd66-4a75-8f73-00fd68929fc7

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
theorem _root_.solution :
    absoluteFrobenius p (Spec (.of (ZMod p))) (𝟙 _) = 𝟙 _ := by
  apply ext_of_isAffine
  ext s
  change s^p = s
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ZMod p))).hom).injective
  exact ((Scheme.ΓSpecIso (.of (ZMod p))).hom.hom.map_pow s p).trans (ZMod.pow_card _)
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
