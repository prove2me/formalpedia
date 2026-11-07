-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialTransvection_mem_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:03.515562+00:00
-- url     : https://prove2.me/submissions/1df6669d-d7cf-4111-8f98-d52338c2eaf3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialTransvection_commutator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    {K : Type*} [Field K] (r : Rank)
    (i j : Fin r.matrixRank) (hij : i ≠ j) (c : K) :
    specialTransvection i j hij c ∈
      commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by
    cases r <;> decide)
  have hik : i ≠ k := Ne.symm hki
  rw [← specialTransvection_commutator i j k hij hik hkj c]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
