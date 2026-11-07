-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.source_boundary2_xTwoBitFilling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:51.043796+00:00
-- url     : https://prove2.me/submissions/b76cc621-bdec-4117-91da-6a794314b3c6

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
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (a : classicalBit) :
    (sourceChainComplex D).boundary2 (xTwoBitFilling D z hFill a) =
      xOneBitSlice z a :=
  Classical.choose_spec
    (((sourceChainComplex D).mem_middleBoundaryCode_iff
      (xOneBitSlice z a)).1 (hFill a))
end QEC.Coding.DistanceBalancing
