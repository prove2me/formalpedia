-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.HammingWeight_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:38.277259+00:00
-- url     : https://prove2.me/submissions/ae5b11d2-493d-4acd-9ddf-a707b80ab9af

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
    {i : Type u} [Fintype i] (w : Word (ZMod 2) i) :
    HammingWeight w = ∑ j : i, if w j ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]
end QEC.Coding.DistanceBalancing
