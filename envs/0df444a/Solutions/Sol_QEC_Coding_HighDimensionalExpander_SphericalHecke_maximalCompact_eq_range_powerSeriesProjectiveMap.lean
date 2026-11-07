-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.maximalCompact_eq_range_powerSeriesProjectiveMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:27:08.138193+00:00
-- url     : https://prove2.me/submissions/1f964440-8095-4db6-86a0-ee6edd42bc45

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d : ℕ) :
    (maximalCompact k d :
      Set (PGL(Fin d, LocalFunctionField k))) =
      Set.range (powerSeriesProjectiveMap k d) := by
  ext g
  constructor
  · intro hg
    obtain ⟨h, rfl⟩ := (mem_maximalCompact_iff k d g).1 hg
    exact ⟨integerGeneralLinearToPowerSeries k d h,
      (integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse k d h).symm⟩
  · rintro ⟨h, rfl⟩
    exact mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact h
end QEC.Coding.HighDimensionalExpander.SphericalHecke
