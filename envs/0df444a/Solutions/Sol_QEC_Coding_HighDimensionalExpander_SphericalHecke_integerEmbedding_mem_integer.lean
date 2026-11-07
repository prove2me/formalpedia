-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integerEmbedding_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:26:28.748827+00:00
-- url     : https://prove2.me/submissions/b71aa59c-44b7-4f0c-b593-03baadd288d6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (f : IntegerRing k) :
    integerEmbedding k f ∈ Valued.integer (LocalFunctionField k) := by
  exact ((LocalTopology.powerSeriesIntegerEquiv k) f).property
end QEC.Coding.HighDimensionalExpander.SphericalHecke
