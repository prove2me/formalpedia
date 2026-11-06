-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepIntegralRoot_mem_upperIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:50:44.940173+00:00
-- url     : https://prove2.me/submissions/06f5771b-2295-43fb-9d0e-2ddebbb51238

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralUniformizer_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_equation

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralRoot P x hx ∈ stepUpperIdeal P x hx := by
  let Q := stepUpperIdeal P x hx
  let w := stepIntegralRoot P x hx
  let t := stepIntegralUniformizer P x hx
  have ht : t ∈ Q := stepIntegralUniformizer_mem_upperIdeal P x hx
  have ht16 : t ^ 16 ∈ Q := Q.pow_mem_of_mem ht 16 (by norm_num)
  have hterm : t ^ 16 * w ^ 15 ∈ Q := Q.mul_mem_right _ ht16
  have hrest : t ^ 16 * w ^ 15 + t ∈ Q := Q.add_mem hterm ht
  have heq : w ^ 16 + t ^ 16 * w ^ 15 + t = 0 :=
    stepIntegralRoot_equation P x hx
  have hw16eq : w ^ 16 = -(t ^ 16 * w ^ 15 + t) := by
    linear_combination heq
  have hw16 : w ^ 16 ∈ Q := hw16eq.symm ▸ Q.neg_mem hrest
  exact (stepUpperIdeal_isMaximal P x hx).isPrime.mem_of_pow_mem 16 hw16
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
