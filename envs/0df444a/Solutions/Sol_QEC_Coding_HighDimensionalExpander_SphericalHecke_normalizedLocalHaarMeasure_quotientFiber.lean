-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_quotientFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:40:41.664132+00:00
-- url     : https://prove2.me/submissions/602d9f90-fa5c-4d9f-a76f-5f484de65c3f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_quotientFiber_eq_preimage_left_mul

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    normalizedLocalHaarMeasure k d
        ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q}) = 1 := by
  rw [quotientFiber_eq_preimage_left_mul,
    MeasureTheory.measure_preimage_mul,
    normalizedLocalHaarMeasure_maximalCompact]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
