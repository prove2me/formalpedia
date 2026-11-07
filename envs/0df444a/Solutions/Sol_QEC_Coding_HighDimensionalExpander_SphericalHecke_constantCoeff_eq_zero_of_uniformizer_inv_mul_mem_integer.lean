-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:26:15.846955+00:00
-- url     : https://prove2.me/submissions/8ea2e38d-5b8e-4f0b-b31b-5cf1c2497671

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integerEmbedding_injective
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
    (k : Type*) [Field k] (f : IntegerRing k)
    (hf : ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f ∈
      Valued.integer (LocalFunctionField k)) :
    PowerSeries.constantCoeff f = 0 := by
  let x : Valued.integer (LocalFunctionField k) :=
    ⟨((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f, hf⟩
  let q : IntegerRing k := (LocalTopology.powerSeriesIntegerEquiv k).symm x
  have hq : integerEmbedding k q =
      ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f := by
    have hx := (LocalTopology.powerSeriesIntegerEquiv k).apply_symm_apply x
    exact congrArg Subtype.val hx
  have hmul := congrArg
    (fun z : LocalFunctionField k ↦ (uniformizerUnit k : LocalFunctionField k) * z) hq
  have hembed : integerEmbedding k (PowerSeries.X * q) = integerEmbedding k f := by
    calc
      integerEmbedding k (PowerSeries.X * q) =
          (uniformizerUnit k : LocalFunctionField k) * integerEmbedding k q := by
        simp [integerEmbedding, coe_uniformizerUnit,
          HahnSeries.ofPowerSeries_X, map_mul]
      _ = (uniformizerUnit k : LocalFunctionField k) *
          (((uniformizerUnit k)⁻¹ : LocalFunctionField k) *
            integerEmbedding k f) := hmul
      _ = integerEmbedding k f := by
        rw [← mul_assoc]
        simp
  have hseries : PowerSeries.X * q = f := integerEmbedding_injective k hembed
  rw [← hseries]
  simp
end QEC.Coding.HighDimensionalExpander.SphericalHecke
