-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankFour_wedgePair_sum_le_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:34.817497+00:00
-- url     : https://prove2.me/submissions/477d3327-a4d8-4f5f-9333-64193586e177

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply


attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (weight : ProjectiveDominantCoweight 3) (p : Fin 6) :
    weight.toDominant.exponent (rankFourWedgeFirst p) +
        weight.toDominant.exponent (rankFourWedgeSecond p) ≤
      weight.toDominant.exponent (0 : Fin 4) +
        weight.toDominant.exponent (1 : Fin 4) := by
  have h01 := weight.toDominant.antitone_exponent
    (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := weight.toDominant.antitone_exponent
    (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := weight.toDominant.antitone_exponent
    (show (2 : Fin 4) ≤ 3 by decide)
  fin_cases p <;>
    simp [rankFourWedgeFirst, rankFourWedgeSecond] <;>
    omega
end QEC.Coding.HighDimensionalExpander.SphericalHecke
