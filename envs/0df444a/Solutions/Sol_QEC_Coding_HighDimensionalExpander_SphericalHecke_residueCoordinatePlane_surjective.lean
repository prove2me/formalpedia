-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.residueCoordinatePlane_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:39.715439+00:00
-- url     : https://prove2.me/submissions/2daf1e08-c9fe-4c3f-9a73-4175e240e52f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesReductionGL_constantGeneralLinearLift
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_exists_generalLinear_map_coordinateGrassmannian


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    Function.Surjective (residueCoordinatePlane k d r hr) := by
  intro W
  obtain ⟨g, hg⟩ :=
    exists_generalLinear_map_coordinateGrassmannian k d r hr W
  refine ⟨constantGeneralLinearLift k d g, ?_⟩
  apply Subtype.ext
  change (coordinateGrassmannian k d r hr).1.map
      (Matrix.GeneralLinearGroup.toLin
        (powerSeriesReductionGL k d (constantGeneralLinearLift k d g))).val = W.1
  rw [powerSeriesReductionGL_constantGeneralLinearLift]
  exact hg
end QEC.Coding.HighDimensionalExpander.SphericalHecke
