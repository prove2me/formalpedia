-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.exists_classicalRightInverse_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:47.721989+00:00
-- url     : https://prove2.me/submissions/c07f9d50-1288-4d6a-b7df-bb6c446091e0

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary)) :
    ∃ S : Matrix classicalBit classicalCheck (ZMod 2),
      IsClassicalRightInverse D S := by
  let f := Matrix.toLin' D.classicalBoundary
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hSurjective)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  change D.classicalBoundary * LinearMap.toMatrix' g = 1
  rw [← LinearMap.toMatrix'_toLin' D.classicalBoundary]
  rw [← LinearMap.toMatrix'_comp]
  rw [hg]
  exact LinearMap.toMatrix'_id
end QEC.Coding.DistanceBalancing
