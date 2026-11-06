-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:33:51.668193+00:00
-- url     : https://prove2.me/submissions/705a6d42-29dd-479a-b2c4-bfa82a734546

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedDivisor_apply_selected
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedDivisor_apply_eq_zero_of_not_mem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (selectedDivisor i).support = selectedPlaces i := by
  classical
  ext P
  rw [Divisor.mem_support_iff]
  constructor
  · intro hcoefficient
    by_contra hP
    exact hcoefficient (selectedDivisor_apply_eq_zero_of_not_mem i P hP)
  · intro hP
    rw [selectedPlaces, Finset.mem_image] at hP
    obtain ⟨j, _, rfl⟩ := hP
    rw [selectedDivisor_apply_selected]
    norm_num
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
