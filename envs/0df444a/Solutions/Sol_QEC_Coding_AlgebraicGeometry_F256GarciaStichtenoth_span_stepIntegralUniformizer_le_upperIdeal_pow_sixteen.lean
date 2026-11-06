-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.span_stepIntegralUniformizer_le_upperIdeal_pow_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:56.588618+00:00
-- url     : https://prove2.me/submissions/e7ab42c8-7d16-4966-a0b8-abd616e58103

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralUniformizer_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_mem_upperIdeal

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal.span ({stepIntegralUniformizer P x hx} :
        Set (StepIntegralClosure P x hx)) ≤
      (stepUpperIdeal P x hx) ^ 16 := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  let Q := stepUpperIdeal P x hx
  let w := stepIntegralRoot P x hx
  let t := stepIntegralUniformizer P x hx
  have ht : t ∈ Q := stepIntegralUniformizer_mem_upperIdeal P x hx
  have hw : w ∈ Q := stepIntegralRoot_mem_upperIdeal P x hx
  have hw16 : w ^ 16 ∈ Q ^ 16 := Ideal.pow_mem_pow hw 16
  have ht16 : t ^ 16 ∈ Q ^ 16 := Ideal.pow_mem_pow ht 16
  have hterm : t ^ 16 * w ^ 15 ∈ Q ^ 16 :=
    (Q ^ 16).mul_mem_right _ ht16
  have hsum : w ^ 16 + t ^ 16 * w ^ 15 ∈ Q ^ 16 :=
    (Q ^ 16).add_mem hw16 hterm
  have heq : w ^ 16 + t ^ 16 * w ^ 15 + t = 0 :=
    stepIntegralRoot_equation P x hx
  have hteq : t = -(w ^ 16 + t ^ 16 * w ^ 15) := by
    linear_combination heq
  change t ∈ Q ^ 16
  rw [hteq]
  exact (Q ^ 16).neg_mem hsum
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
