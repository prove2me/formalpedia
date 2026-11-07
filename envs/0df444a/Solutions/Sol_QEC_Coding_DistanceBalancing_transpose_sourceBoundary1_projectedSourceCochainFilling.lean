-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.transpose_sourceBoundary1_projectedSourceCochainFilling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:27:44.331197+00:00
-- url     : https://prove2.me/submissions/b3bd33b9-7fd1-47e4-9f50-59b3d38b7b62

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
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier)
    (a : classicalBit) :
    wordLinearMapTranspose (sourceChainComplex D).boundary1
      (projectedSourceCochainFilling D S x hFill a) =
        projectedSourceCochain D S x a :=
  Classical.choose_spec
    (((sourceChainComplex D).mem_firstCoboundaryCheckCode_iff
      (projectedSourceCochain D S x a)).1 (hFill a))
end QEC.Coding.DistanceBalancing
