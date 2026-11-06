-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicPolynomial_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:56.486388+00:00
-- url     : https://prove2.me/submissions/f54beebf-cba3-4fce-8edc-64f50b3617cc

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
section
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
private theorem rationalAdicGenerator_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    Submodule.IsPrincipal.generator p.asIdeal ≠ 0 := by
  intro hzero
  apply p.ne_bot
  exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p.asIdeal).2 hzero
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicDecidableEq
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (rationalAdicPolynomial p).Monic := by
  change (normalize (Submodule.IsPrincipal.generator p.asIdeal)).Monic
  exact Polynomial.monic_normalize (rationalAdicGenerator_ne_zero p)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
