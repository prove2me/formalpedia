-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:47:40.222552+00:00
-- url     : https://prove2.me/submissions/33b27bfb-c916-4080-b923-8a90be8129fd

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
    (quadraticArtinSchreierIntegralRoot P a ha :
        QuadraticArtinSchreierField P a ha) =
      quadraticArtinSchreierReciprocalRoot P a ha :=
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
