-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourHecke_ne_zero_iff_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:16.931142+00:00
-- url     : https://prove2.me/submissions/53dd4cf4-d80c-479d-a10d-59a9bf82fc11

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalHeckeFunction_ne_zero_iff_adjacent

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (color : RankFourColor)
    (gx gy : HeckeGroup k 4) :
    fundamentalHeckeFunction k 4 (color.val + 1) (gx⁻¹ * gy) ≠ 0 ↔
      RankFourAdjacent k color (QuotientGroup.mk gx) (QuotientGroup.mk gy) :=
  fundamentalHeckeFunction_ne_zero_iff_adjacent k 4 (color.val + 1) gx gy
end QEC.Coding.HighDimensionalExpander.SphericalHecke
