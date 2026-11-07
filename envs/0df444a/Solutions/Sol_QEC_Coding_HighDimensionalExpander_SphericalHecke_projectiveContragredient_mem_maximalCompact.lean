-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveContragredient_mem_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:18.621419+00:00
-- url     : https://prove2.me/submissions/17b0bedf-e59f-483d-8b98-d822289a6742

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_contragredient_integralGeneralLinearToLocal

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] {d : ℕ}
    {g : PGL(Fin d, LocalFunctionField k)}
    (hg : g ∈ maximalCompact k d) :
    projectiveContragredientHom g ∈ maximalCompact k d := by
  rw [mem_maximalCompact_iff] at hg ⊢
  obtain ⟨A, rfl⟩ := hg
  refine ⟨contragredientGeneralLinearHom A, ?_⟩
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k d
        (contragredientGeneralLinearHom A)) =
    projectiveContragredientHom (Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k d A))
  rw [← contragredient_integralGeneralLinearToLocal]
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
