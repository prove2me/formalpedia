-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:47:40.982556+00:00
-- url     : https://prove2.me/submissions/5708d04c-d810-4be1-a357-c00ae195eb53

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierIntegralUniformizer P a ha :
        QuadraticArtinSchreierField P a ha) =
      quadraticArtinSchreierEmbedding P a ha a⁻¹ :=
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
