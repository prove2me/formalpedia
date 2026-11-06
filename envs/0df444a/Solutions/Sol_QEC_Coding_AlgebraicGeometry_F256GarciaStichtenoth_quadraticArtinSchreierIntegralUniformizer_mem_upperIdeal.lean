-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:49:02.657147+00:00
-- url     : https://prove2.me/submissions/3e1bff19-b278-4c58-8090-ed4ec8736ca5

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
    quadraticArtinSchreierIntegralUniformizer P a ha ∈
      quadraticArtinSchreierUpperIdeal P a ha := by
  have hover := (quadraticArtinSchreierUpperIdeal_liesOver P a ha).over
  have hbase : reciprocalUniformizer P a ha ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P a ha]
    exact Ideal.mem_span_singleton_self _
  change algebraMap P.valuationRing
      (QuadraticArtinSchreierIntegralClosure P a ha)
      (reciprocalUniformizer P a ha) ∈
        quadraticArtinSchreierUpperIdeal P a ha
  change reciprocalUniformizer P a ha ∈
    Ideal.under P.valuationRing (quadraticArtinSchreierUpperIdeal P a ha)
  rw [← hover]
  exact hbase
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
