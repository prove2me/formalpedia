-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:44:37.22034+00:00
-- url     : https://prove2.me/submissions/6ebb56e4-0d91-4133-b661-27b4902726ea

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.ProjectiveDeterminant
theorem _root_.solution (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.ProjGenLinGroup.mk g ∈ specialProjectiveSubgroup ↔
      ∃ r : Kˣ, r ^ 2 = Matrix.GeneralLinearGroup.det g := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hs
    refine ⟨r, ?_⟩
    have hDet := congrArg Matrix.GeneralLinearGroup.det hr
    simpa using hDet
  · rintro ⟨r, hr⟩
    have hDet : Matrix.GeneralLinearGroup.det
        (g * Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹) = 1 := by
      rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
        ← hr, inv_pow, mul_inv_cancel]
    let s : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨(g * Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹).val,
        congrArg Units.val hDet⟩
    refine ⟨s, ?_⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s) =
      Matrix.ProjGenLinGroup.mk g
    have hs : Matrix.SpecialLinearGroup.toGL s =
        g * Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹ := Units.ext rfl
    rw [hs, map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
end QEC.Coding.ExpanderCodes.ProjectiveDeterminant
