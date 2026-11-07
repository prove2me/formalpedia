-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.smithLeft_mem_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:45:11.442404+00:00
-- url     : https://prove2.me/submissions/1f0aed75-d3a0-4306-893a-37ee8c2a330a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk
        (smithLeftGeneralLinearLocal (k := k) (d := d) A) ∈
      maximalCompact k d :=
  mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
    (smithLeftGeneralLinear (k := k) (d := d) A)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
