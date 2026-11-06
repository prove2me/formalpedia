-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralUniformizer_mem_upperIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:48:13.84833+00:00
-- url     : https://prove2.me/submissions/0e784b0f-22f3-4c44-aa5f-e4bdaf50eced

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralUniformizer P x hx ∈ sourceStepUpperIdeal P x hx := by
  have hover := (sourceStepUpperIdeal_liesOver P x hx).over
  have hbase : sourceStepUniformizer P x hx ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx)]
    exact Ideal.mem_span_singleton_self _
  change algebraMap P.valuationRing (SourceStepIntegralClosure P x hx)
      (sourceStepUniformizer P x hx) ∈ sourceStepUpperIdeal P x hx
  change sourceStepUniformizer P x hx ∈
    Ideal.under P.valuationRing (sourceStepUpperIdeal P x hx)
  rw [← hover]
  exact hbase
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
