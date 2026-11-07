-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesReductionGL_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:34.638131+00:00
-- url     : https://prove2.me/submissions/ac6dc1e4-cb99-4990-b494-5cd44706b54a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesReductionGL_constantGeneralLinearLift

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d : ℕ) :
    Function.Surjective (powerSeriesReductionGL k d) := by
  intro g
  exact ⟨constantGeneralLinearLift k d g,
    powerSeriesReductionGL_constantGeneralLinearLift k d g⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
