-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankThree_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:57.848798+00:00
-- url     : https://prove2.me/submissions/81e88ff2-71d6-4123-8dd6-16fecf78ac12

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankThree_two

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 3 (fundamentalDoubleCoset k 3 2) =
      (Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankThree_two]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
