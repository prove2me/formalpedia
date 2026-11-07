-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankThree_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:56.775143+00:00
-- url     : https://prove2.me/submissions/1d0c6cf8-93f9-46d7-9051-0c78498f54fe

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankThree_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 3 (fundamentalDoubleCoset k 3 1) =
      (Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankThree_one]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
