-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeHecke_ne_zero_iff_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:15.161203+00:00
-- url     : https://prove2.me/submissions/9da84e6c-a371-4adc-8a64-030cc14e8ae5

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
    (k : Type u) [Field k] [Finite k] (color : RankThreeColor)
    (gx gy : HeckeGroup k 3) :
    fundamentalHeckeFunction k 3 (color.val + 1) (gx⁻¹ * gy) ≠ 0 ↔
      RankThreeAdjacent k color (QuotientGroup.mk gx) (QuotientGroup.mk gy) :=
  fundamentalHeckeFunction_ne_zero_iff_adjacent k 3 (color.val + 1) gx gy
end QEC.Coding.HighDimensionalExpander.SphericalHecke
