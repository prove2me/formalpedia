-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_of_classical_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:32.068514+00:00
-- url     : https://prove2.me/submissions/22e45bd5-f3a5-4a53-bd21-461acfe84d79

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_exists_classicalRightInverse_of_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancing_middleHomologyDistanceAtLeast

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
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d) :
    MiddleHomologyDistanceAtLeast (chainComplex D) d := by
  obtain ⟨S, hS⟩ := exists_classicalRightInverse_of_surjective D hSurjective
  exact middleHomologyDistanceAtLeast D S hS hDistance
end QEC.Coding.DistanceBalancing
