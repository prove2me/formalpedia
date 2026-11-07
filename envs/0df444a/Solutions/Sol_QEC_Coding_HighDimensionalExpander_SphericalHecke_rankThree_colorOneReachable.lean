-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThree_colorOneReachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:50.796178+00:00
-- url     : https://prove2.me/submissions/61d32af8-a613-452c-b94f-e4933e5ef27d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantCoweight_rankThree_colorOneReachable
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_colorOneReachable_of_projectiveDominant

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (q : BuildingVertex k 3) :
    ColorOneReachable k 3 (QuotientGroup.mk 1) q := by
  exact colorOneReachable_of_projectiveDominant k 2
    (projectiveDominantCoweight_rankThree_colorOneReachable k) q
end QEC.Coding.HighDimensionalExpander.SphericalHecke
