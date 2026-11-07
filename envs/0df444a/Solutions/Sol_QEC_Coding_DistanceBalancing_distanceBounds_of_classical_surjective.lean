-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.distanceBounds_of_classical_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:39.475071+00:00
-- url     : https://prove2.me/submissions/fd6234d3-05c1-420c-8b23-e79b188f0810

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_middleHomologyDistanceAtLeast_mul_of_classical_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancing_middleCohomologyDistanceAtLeast_of_classical_surjective

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
    {dHomology dCohomology dClassical : Nat}
    (hHomology : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dHomology)
    (hCohomology : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) dCohomology)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
        (chainComplex D) (dClassical * dHomology) ∧
      MiddleCohomologyDistanceAtLeast
        (chainComplex D) dCohomology := by
  exact ⟨
    middleHomologyDistanceAtLeast_mul_of_classical_surjective
      D hSurjective hHomology hClassical,
    middleCohomologyDistanceAtLeast_of_classical_surjective
      D hSurjective hCohomology⟩
end QEC.Coding.DistanceBalancing
