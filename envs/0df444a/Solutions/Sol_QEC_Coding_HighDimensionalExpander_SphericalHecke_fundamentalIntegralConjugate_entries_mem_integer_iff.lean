-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_entries_mem_integer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:27:19.649835+00:00
-- url     : https://prove2.me/submissions/dbae3a2f-0ac2-4110-bc7c-69b558ad5534

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integerEmbedding_mem_integer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
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
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    (∀ i j, fundamentalIntegralConjugate k d r g i j ∈
      Valued.integer (LocalFunctionField k)) ↔
      UpperRightResidueZero k d r g := by
  constructor
  · intro h i j hi hj
    apply constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer k
    have hij := h i j
    rw [fundamentalIntegralConjugate_apply] at hij
    simp only [if_pos hi, if_neg (not_lt.mpr hj), mul_one] at hij
    exact hij
  · intro h i j
    rw [fundamentalIntegralConjugate_apply]
    by_cases hi : i.val < r
    · by_cases hj : j.val < r
      · simp only [if_pos hi, if_pos hj]
        rw [show ((uniformizerUnit k)⁻¹ : LocalFunctionField k) *
            integerEmbedding k (g i j) *
              (uniformizerUnit k : LocalFunctionField k) =
            integerEmbedding k (g i j) by
          calc
            _ = ((uniformizerUnit k)⁻¹ : LocalFunctionField k) *
                (uniformizerUnit k : LocalFunctionField k) *
                  integerEmbedding k (g i j) := by ac_rfl
            _ = _ := by simp]
        exact integerEmbedding_mem_integer k (g i j)
      · simp only [if_pos hi, if_neg hj, mul_one]
        rw [uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
          k (g i j) (h i j hi (not_lt.mp hj))]
        exact integerEmbedding_mem_integer k (powerSeriesTail k (g i j))
    · by_cases hj : j.val < r
      · simp only [if_neg hi, if_pos hj, one_mul]
        change integerEmbedding k (g i j) *
          (uniformizerUnit k : LocalFunctionField k) ∈ _
        have hX : (uniformizerUnit k : LocalFunctionField k) ∈
            Valued.integer (LocalFunctionField k) := by
          simpa [coe_uniformizerUnit, integerEmbedding,
            HahnSeries.ofPowerSeries_X] using
            (integerEmbedding_mem_integer k (PowerSeries.X : IntegerRing k))
        exact (Valued.integer (LocalFunctionField k)).mul_mem
          (integerEmbedding_mem_integer k (g i j)) hX
      · simp only [if_neg hi, if_neg hj, one_mul, mul_one]
        exact integerEmbedding_mem_integer k (g i j)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
