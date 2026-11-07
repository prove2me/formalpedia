-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projective_mk_mem_maximalCompact_iff_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:48.564192+00:00
-- url     : https://prove2.me/submissions/f693de49-c8fe-4459-a297-7754d567e030

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_scalar_mul_eq_of_projective_mk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinear_det_localUnitOrder_eq_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] [Finite k] (d : ℕ) (hd : 0 < d)
    (A : GL (Fin d) (LocalFunctionField k))
    (hdet : localUnitOrder (Matrix.GeneralLinearGroup.det A) = 0) :
    Matrix.ProjGenLinGroup.mk A ∈ maximalCompact k d ↔
      A ∈ integralGeneralLinearSet k d := by
  constructor
  · intro hA
    obtain ⟨B, hB⟩ := (mem_maximalCompact_iff k d _).mp hA
    change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k d B) = Matrix.ProjGenLinGroup.mk A at hB
    obtain ⟨c, hGL⟩ :=
      exists_scalar_mul_eq_of_projective_mk_eq hB.symm
    have horder := congrArg localUnitOrder
      (congrArg Matrix.GeneralLinearGroup.det hGL)
    have hc : localUnitOrder c = 0 := by
      simp [Matrix.GeneralLinearGroup.det_scalar, localUnitOrder_mul,
        localUnitOrder_pow, integralGeneralLinear_det_localUnitOrder_eq_zero,
        hdet] at horder
      omega
    let ci := integerUnitOfLocalUnitOrderZero k c hc
    rw [← range_integralGeneralLinearToLocal]
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) ci * B, ?_⟩
    calc
      integralGeneralLinearToLocal k d
          (Matrix.GeneralLinearGroup.scalar (Fin d) ci * B) =
          Matrix.GeneralLinearGroup.scalar (Fin d) c *
            integralGeneralLinearToLocal k d B := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        simp [ci, integerUnitOfLocalUnitOrderZero,
          integralGeneralLinearToLocal, Matrix.mul_apply]
      _ = A := hGL.symm
  · intro hA
    rw [← range_integralGeneralLinearToLocal] at hA
    obtain ⟨B, rfl⟩ := hA
    exact (mem_maximalCompact_iff k d _).mpr ⟨B, rfl⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
