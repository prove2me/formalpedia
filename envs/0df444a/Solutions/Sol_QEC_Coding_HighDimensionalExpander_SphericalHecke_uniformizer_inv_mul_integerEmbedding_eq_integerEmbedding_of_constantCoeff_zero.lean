-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:26:11.832203+00:00
-- url     : https://prove2.me/submissions/334a7375-fd23-438a-b82e-c7816db7511f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
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
    (k : Type*) [Field k] (f : IntegerRing k)
    (hf : PowerSeries.constantCoeff f = 0) :
    ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f =
      integerEmbedding k (powerSeriesTail k f) := by
  let q := powerSeriesTail k f
  have hfq : f = PowerSeries.X * q := by
    simpa [hf, q, powerSeriesTail] using (PowerSeries.eq_X_mul_shift_add_const f)
  change ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f =
    integerEmbedding k q
  rw [hfq]
  simp [integerEmbedding, coe_uniformizerUnit, HahnSeries.ofPowerSeries_X,
    map_mul, ← mul_assoc]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
