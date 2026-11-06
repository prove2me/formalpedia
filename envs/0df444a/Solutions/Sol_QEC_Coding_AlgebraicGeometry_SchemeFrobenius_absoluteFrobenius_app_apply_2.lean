-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_app_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:38.05254+00:00
-- url     : https://prove2.me/submissions/9945632b-533f-4ee8-b1bc-fd1194bf69d5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_sectionPower_apply

set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))
namespace QEC.Coding.AlgebraicGeometry.SchemeFrobenius
theorem _root_.solution (U : X.Opens) (s : Γ(X, U)) :
    (absoluteFrobenius p X f).app U s = s^p := sectionPower_apply p X f U s
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
