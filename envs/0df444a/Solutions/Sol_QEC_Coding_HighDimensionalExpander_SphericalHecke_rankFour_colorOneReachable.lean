-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFour_colorOneReachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:54.790418+00:00
-- url     : https://prove2.me/submissions/cd3c95db-ccd8-4fc9-a248-15a37c0f5979

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantCoweight_rankFour_colorOneReachable
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_colorOneReachable_of_projectiveDominant

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (q : BuildingVertex k 4) :
    ColorOneReachable k 4 (QuotientGroup.mk 1) q := by
  exact colorOneReachable_of_projectiveDominant k 3
    (projectiveDominantCoweight_rankFour_colorOneReachable k) q
end QEC.Coding.HighDimensionalExpander.SphericalHecke
