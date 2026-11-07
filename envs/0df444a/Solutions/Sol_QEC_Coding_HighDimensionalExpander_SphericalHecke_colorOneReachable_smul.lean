-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.colorOneReachable_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:34:25.341444+00:00
-- url     : https://prove2.me/submissions/74988f46-d413-4af1-af5d-9bf496bb0942

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
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (g : HeckeGroup k d) {x y : BuildingVertex k d}
    (hxy : ColorOneReachable k d x y) :
    ColorOneReachable k d (g • x) (g • y) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact ih.tail
        ((coloredBuildingAdjacent_smul_iff k d 1 g _ _).2 hbc)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
