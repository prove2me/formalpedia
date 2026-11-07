-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.coloredAdjacencyDegree_eq_ncard_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:55.437563+00:00
-- url     : https://prove2.me/submissions/0071822c-6364-4a2f-a331-863a96467848

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    coloredAdjacencyDegree k d r =
      {x : BuildingVertex k d |
        ColoredBuildingAdjacent k d r (QuotientGroup.mk 1) x}.ncard := by
  rw [coloredAdjacencyDegree, fundamentalNeighborCosets,
    ← Set.ncard_eq_toFinset_card (fundamentalNeighborCosetSet k d r)
      (fundamentalNeighborCosetSet_finite k d r)]
  apply congrArg Set.ncard
  ext x
  exact mem_fundamentalNeighborCosetSet_iff_adjacent_base k d r x
end QEC.Coding.HighDimensionalExpander.SphericalHecke
