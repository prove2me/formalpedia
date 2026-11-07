-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveDeterminant.conjugate_mem_specialProjectiveSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:30:54.658391+00:00
-- url     : https://prove2.me/submissions/23228cd3-4aa3-4e20-a253-2bcf08f7f325

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_mk_mem_specialProjectiveSubgroup_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.ProjectiveDeterminant
theorem _root_.solution (c g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) :
    c * g * c⁻¹ ∈ specialProjectiveSubgroup := by
  induction c using Matrix.ProjGenLinGroup.induction_on with | mk c =>
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  rw [mk_mem_specialProjectiveSubgroup_iff] at hg
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_specialProjectiveSubgroup_iff]
  obtain ⟨r, hr⟩ := hg
  refine ⟨r, ?_⟩
  simpa [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc] using hr
end QEC.Coding.ExpanderCodes.ProjectiveDeterminant
