-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.middleCohomologyDistanceAtLeast_of_classical_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:41:30.243243+00:00
-- url     : https://prove2.me/submissions/3154113e-df01-436b-a1c9-5706f7817884

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_middleCohomologyDistanceAtLeast
import Theorems.Thm_QEC_Coding_DistanceBalancing_exists_classicalRightInverse_of_surjective

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
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d) :
    MiddleCohomologyDistanceAtLeast (chainComplex D) d := by
  obtain ⟨S, hS⟩ := exists_classicalRightInverse_of_surjective D hSurjective
  exact middleCohomologyDistanceAtLeast D S hS hDistance
end QEC.Coding.DistanceBalancing
