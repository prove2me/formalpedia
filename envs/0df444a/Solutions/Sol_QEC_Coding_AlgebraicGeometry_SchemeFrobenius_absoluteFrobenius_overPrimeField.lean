-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_overPrimeField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:50.209021+00:00
-- url     : https://prove2.me/submissions/c27da88e-9f7e-4c83-9b62-fa08b1584c4d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_natural
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_primeSpec_id

set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))
namespace QEC.Coding.AlgebraicGeometry.SchemeFrobenius
theorem _root_.solution : absoluteFrobenius p X f ≫ f = f :=
  (absoluteFrobenius_natural p X f f (𝟙 _)).trans
    ((congrArg (fun r => f ≫ r) (absoluteFrobenius_primeSpec_id p)).trans (Category.comp_id f))
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
