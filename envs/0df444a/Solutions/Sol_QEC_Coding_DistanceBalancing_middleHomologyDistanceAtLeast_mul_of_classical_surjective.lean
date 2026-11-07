-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_mul_of_classical_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:49.336221+00:00
-- url     : https://prove2.me/submissions/7d14e9d3-0d3f-4476-88e3-dfb8591ea4cd

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_exists_classicalRightInverse_of_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancing_middleHomologyDistanceAtLeast_mul

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
      (Matrix.toLin' D.classicalBoundary))
    {dSource dClassical : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
      (chainComplex D) (dClassical * dSource) := by
  obtain ⟨S, hS⟩ := exists_classicalRightInverse_of_surjective D hSurjective
  exact middleHomologyDistanceAtLeast_mul
    D S hS hSource hClassical
end QEC.Coding.DistanceBalancing
