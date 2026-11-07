-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.middleCohomologyDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:39:53.732635+00:00
-- url     : https://prove2.me/submissions/cc686fca-ca57-4f39-92e2-ec9e694c07f3

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_mem_firstCoboundary_of_weight_lt
import Theorems.Thm_QEC_Coding_DistanceBalancing_mem_firstCoboundaryCheckCode_of_projected_slices

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
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {d : Nat}
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d) :
    MiddleCohomologyDistanceAtLeast (chainComplex D) d := by
  intro x hx hNonboundary
  by_contra hNotLower
  have hWeight : HammingWeight x < d := by omega
  have hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier := by
    intro a
    exact projectedSourceCochain_mem_firstCoboundary_of_weight_lt
      D S hS hDistance x hx hWeight a
  exact hNonboundary
    (mem_firstCoboundaryCheckCode_of_projected_slices
      D S hS x hx hFill)
end QEC.Coding.DistanceBalancing
