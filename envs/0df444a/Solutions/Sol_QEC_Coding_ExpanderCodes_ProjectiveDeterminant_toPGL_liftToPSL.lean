-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:44:50.938815+00:00
-- url     : https://prove2.me/submissions/5fcbb56e-1c7d-45cd-973e-477a07a5e75e

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveDeterminant
open Matrix
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.ProjectiveDeterminant
theorem _root_.solution (g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (liftToPSL g hg) = g :=
  MonoidHom.apply_ofInjective_symm Matrix.ProjectiveSpecialLinearGroup.toPGL_injective _
end QEC.Coding.ExpanderCodes.ProjectiveDeterminant
