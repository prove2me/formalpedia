-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:38.877138+00:00
-- url     : https://prove2.me/submissions/4fc34fe9-47bc-4a0b-9408-b22049ec05e3

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_exists_detectingClassicalWord_of_product_nonboundary
import Theorems.Thm_QEC_Coding_DistanceBalancing_distance_product_le_of_detectingClassicalWord

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
    {dSource dClassical : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
      (chainComplex D) (dClassical * dSource) := by
  intro z hz hNonboundary
  obtain ⟨w, hwKernel, hwNonzero, hwBound⟩ :=
    exists_detectingClassicalWord_of_product_nonboundary
      D S hS hSource z hz hNonboundary
  exact distance_product_le_of_detectingClassicalWord
    D hClassical w hwKernel hwNonzero hwBound
end QEC.Coding.DistanceBalancing
