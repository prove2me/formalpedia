-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:34.410191+00:00
-- url     : https://prove2.me/submissions/4905ab4e-4dc5-43a9-8be3-b22d75048ffd

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
theorem _root_.solution (x : X) : absoluteFrobenius p X f x = x := rfl
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
