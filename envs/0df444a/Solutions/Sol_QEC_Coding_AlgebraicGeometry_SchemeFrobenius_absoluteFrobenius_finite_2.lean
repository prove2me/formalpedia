-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:55.875219+00:00
-- url     : https://prove2.me/submissions/2213f4c8-4027-4e4e-ba08-875fa245b38a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_sectionBase_finiteType
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_finite


set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))
namespace QEC.Coding.AlgebraicGeometry.SchemeFrobenius
theorem _root_.solution [LocallyOfFiniteType f] :
    IsFinite (absoluteFrobenius p X f) := by
  refine { isAffine_preimage := ?_, finite_app := ?_ }
  · intro U hU
    exact hU
  · intro U hU
    let : Algebra (ZMod p) Γ(X, U) := (sectionBase p X f U).toAlgebra
    let : Algebra.FiniteType (ZMod p) Γ(X, U) := sectionBase_finiteType p X f U hU
    exact primeAlgebraFrobenius_finite p Γ(X, U)
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius
