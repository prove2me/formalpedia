-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_eq_iff_upperRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:17.088674+00:00
-- url     : https://prove2.me/submissions/63d22f84-f325-4db1-a513-3ff9e057b66f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_upperRightResidueZero_iff_reduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_map_coordinateGrassmannian_eq_self_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_map_generalLinear_eq_map_iff
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
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h ↔
      UpperRightResidueZero k d r (g⁻¹ * h)⁻¹ := by
  let P := (coordinateGrassmannian k d r hr).1
  let cg := contragredientGeneralLinearHom (powerSeriesReductionGL k d g)
  let ch := contragredientGeneralLinearHom (powerSeriesReductionGL k d h)
  have hmatrix :
      P.map (Matrix.GeneralLinearGroup.toLin cg).val =
          P.map (Matrix.GeneralLinearGroup.toLin ch).val ↔
        UpperRightResidueZero k d r (g⁻¹ * h)⁻¹ := by
    rw [map_generalLinear_eq_map_iff]
    have hrel : cg⁻¹ * ch = contragredientGeneralLinearHom
        (powerSeriesReductionGL k d (g⁻¹ * h)) := by
      simp [cg, ch]
    rw [hrel]
    rw [map_coordinateGrassmannian_eq_self_iff]
    rw [upperRightResidueZero_iff_reduction]
    constructor
    · intro hb i j hi hj
      have hzero := hb j i hj hi
      change (powerSeriesReductionGL k d (g⁻¹ * h))⁻¹ i j = 0 at hzero
      change powerSeriesReductionGL k d ((g⁻¹ * h)⁻¹) i j = 0
      simpa using hzero
    · intro hb i j hi hj
      have hzero := hb j i hj hi
      change powerSeriesReductionGL k d ((g⁻¹ * h)⁻¹) j i = 0 at hzero
      change (powerSeriesReductionGL k d (g⁻¹ * h))⁻¹ j i = 0
      simpa using hzero
  constructor
  · intro h
    apply hmatrix.mp
    have hv := congrArg Subtype.val h
    change P.map (Matrix.GeneralLinearGroup.toLin cg).val =
      P.map (Matrix.GeneralLinearGroup.toLin ch).val at hv
    exact hv
  · intro h
    apply Subtype.ext
    change P.map (Matrix.GeneralLinearGroup.toLin cg).val =
      P.map (Matrix.GeneralLinearGroup.toLin ch).val
    exact hmatrix.mpr h
end QEC.Coding.HighDimensionalExpander.SphericalHecke
