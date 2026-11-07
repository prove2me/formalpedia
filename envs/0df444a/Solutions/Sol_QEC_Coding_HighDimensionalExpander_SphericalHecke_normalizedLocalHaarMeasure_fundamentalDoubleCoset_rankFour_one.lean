-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:03.608356+00:00
-- url     : https://prove2.me/submissions/2aac9fd5-6c2d-4866-8e55-ceef8f966f8f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankFour_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 4 (fundamentalDoubleCoset k 4 1) =
      (Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankFour_one]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
