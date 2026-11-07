-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:45:06.219979+00:00
-- url     : https://prove2.me/submissions/369ffef2-129f-46e3-9613-4e0ba9d03564

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_mk_mem_specialProjectiveSubgroup_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.ProjectiveDeterminant
theorem _root_.solution
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.ProjGenLinGroup.mk g ∈ specialProjectiveSubgroup ↔
      ∃ r : K, r ^ 2 = (Matrix.GeneralLinearGroup.det g : K) := by
  rw [mk_mem_specialProjectiveSubgroup_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, congrArg Units.val hr⟩
  · rintro ⟨r, hr⟩
    have hR : r ≠ 0 := by
      intro hZero
      exact (Matrix.GeneralLinearGroup.det g).ne_zero
        (by simpa [hZero] using hr.symm)
    exact ⟨Units.mk0 r hR, Units.ext (by simpa using hr)⟩
end QEC.Coding.ExpanderCodes.ProjectiveDeterminant
