-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.exists_homologyFunctional_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:37:23.282882+00:00
-- url     : https://prove2.me/submissions/a866652a-cd64-4b08-9d73-ac118094467f

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
    {x : (sourceChainComplex D).middleHomology}
    (hx : x ≠ 0) :
    ∃ φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology,
      φ x = 1 :=
  Module.Projective.exists_dual_eq_one (ZMod 2) hx
end QEC.Coding.DistanceBalancing
