-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:52.510593+00:00
-- url     : https://prove2.me/submissions/f8c3f05f-fbfd-40a8-bbed-b4e0afd4bde0

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicDecidableEq
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    Irreducible (rationalAdicPolynomial p) := by
  change Irreducible (normalize (Submodule.IsPrincipal.generator p.asIdeal))
  have hprime : Prime (Submodule.IsPrincipal.generator p.asIdeal) :=
    Submodule.IsPrincipal.prime_generator_of_isPrime p.asIdeal p.ne_bot
  exact ((associated_normalize _).prime hprime).irreducible
end QEC.Coding.AlgebraicGeometry.GlobalPlace
