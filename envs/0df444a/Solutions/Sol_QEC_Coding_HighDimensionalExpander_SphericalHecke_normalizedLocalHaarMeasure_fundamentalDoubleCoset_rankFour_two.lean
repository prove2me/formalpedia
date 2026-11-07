-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:06.490019+00:00
-- url     : https://prove2.me/submissions/e8508124-0932-4167-b8e3-25a23bc695d4

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankFour_two

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 4 (fundamentalDoubleCoset k 4 2) =
      ((Nat.card k ^ 2 + 1) * (Nat.card k ^ 2 + Nat.card k + 1) : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankFour_two]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
