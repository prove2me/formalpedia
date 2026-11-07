-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_commutator_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:04:40.770393+00:00
-- url     : https://prove2.me/submissions/76cb9de4-8aed-489f-bfc3-7ba2df0f549c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearGroup_commutator_eq_top
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearToPSL_surjective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    commutator (PSL P r level) = ⊤ := by
  letI : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level)) :=
    ⟨specialLinearGroup_commutator_eq_top r⟩
  letI : Group.IsPerfect (PSL P r level) :=
    Group.IsPerfect.ofSurjective
      (specialLinearToPSL_surjective P r level)
  exact Group.IsPerfect.commutator_eq_top
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
