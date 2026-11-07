-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.mem_firstCoboundaryCheckCode_of_projected_slices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:19.133111+00:00
-- url     : https://prove2.me/submissions/f676484d-5c36-4982-be50-4eb4a98c2ff3

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary1_productCochainFilling

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
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier) :
    x ∈ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  apply ((chainComplex D).mem_firstCoboundaryCheckCode_iff x).2
  exact ⟨productCochainFilling D S x hFill,
    transpose_boundary1_productCochainFilling D S hS x hx hFill⟩
end QEC.Coding.DistanceBalancing
